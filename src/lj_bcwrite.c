/*
** Bytecode writer.
** Copyright (C) 2005-2020 Mike Pall. See Copyright Notice in luajit.h
*/

#define lj_bcwrite_c
#define LUA_CORE

#include "lj_obj.h"
#include "lj_gc.h"
#include "lj_buf.h"
#include "lj_bc.h"
#if LJ_HASFFI
#include "lj_ctype.h"
#endif
#if LJ_HASJIT
#include "lj_dispatch.h"
#include "lj_jit.h"
#endif
#include "lj_strfmt.h"
#include "lj_bcdump.h"
#include "lj_vm.h"

/* Context for bytecode writer. */
typedef struct BCWriteCtx {
  SBuf sb;			/* Output buffer. */
  GCproto *pt;			/* Root prototype. */
  lua_Writer wfunc;		/* Writer callback. */
  void *wdata;			/* Writer callback data. */
  int strip;			/* Strip debug info. */
  int status;			/* Status from writer callback. */
} BCWriteCtx;

/* -- Bytecode writer ----------------------------------------------------- */

/* Write a single constant key/value of a template table. */
static void bcwrite_ktabk(BCWriteCtx *ctx, cTValue *o, int narrow)
{
  char *p = lj_buf_more(&ctx->sb, 1+10);
  if (tvisstr(o)) {                           // 字符串
    const GCstr *str = strV(o);
    MSize len = str->len;
    p = lj_buf_more(&ctx->sb, 5+len);
    p = lj_strfmt_wuleb128(p, BCDUMP_KTAB_STR+len);
    p = lj_buf_wmem(p, strdata(str), len);
  } else if (tvisint(o)) {                    // 整型
    *p++ = BCDUMP_KTAB_INT;
    p = lj_strfmt_wuleb128(p, intV(o));
  } else if (tvisnum(o)) {                    // 浮点型
    if (!LJ_DUALNUM && narrow) {  /* Narrow number constants to integers. */
      lua_Number num = numV(o);
      int32_t k = lj_num2int(num);
      if (num == (lua_Number)k) {  /* -0 is never a constant. */
        *p++ = BCDUMP_KTAB_INT;
        p = lj_strfmt_wuleb128(p, k);
        setsbufP(&ctx->sb, p);
        return;
      }
    }
    *p++ = BCDUMP_KTAB_NUM;
    p = lj_strfmt_wuleb128(p, o->u32.lo);
    p = lj_strfmt_wuleb128(p, o->u32.hi);
  } else {
    lua_assert(tvispri(o));
    *p++ = BCDUMP_KTAB_NIL+~itype(o);
  }
  setsbufP(&ctx->sb, p);
}

/* Write a template table. */
static void bcwrite_ktab(BCWriteCtx *ctx, char *p, const GCtab *t)
{
  MSize narray = 0, nhash = 0;
  if (t->asize > 0) {  /* Determine max. length of array part. */
    ptrdiff_t i;
    TValue *array = tvref(t->array);
    for (i = (ptrdiff_t)t->asize-1; i >= 0; i--)
      if (!tvisnil(&array[i]))
	break;
    narray = (MSize)(i+1);
  }
  if (t->hmask > 0) {  /* Count number of used hash slots. */
    MSize i, hmask = t->hmask;
    Node *node = noderef(t->node);
    for (i = 0; i <= hmask; i++)
      nhash += !tvisnil(&node[i].val);
  }
  
  /* Write number of array slots and hash slots. */
  p = lj_strfmt_wuleb128(p, narray);    // 基于数组的ArrayItem
  p = lj_strfmt_wuleb128(p, nhash);     // 基于Hash的HashItem
  setsbufP(&ctx->sb, p);

  if (narray) {  /* Write array entries (may contain nil). */
    MSize i;
    TValue *o = tvref(t->array);
    for (i = 0; i < narray; i++, o++)
      bcwrite_ktabk(ctx, o, 1);
  }
  
  if (nhash) {  /* Write hash entries. */
    MSize i = nhash;
    Node *node = noderef(t->node) + t->hmask;
    for (;; node--)
      if (!tvisnil(&node->val)) {
        bcwrite_ktabk(ctx, &node->key, 0);
        bcwrite_ktabk(ctx, &node->val, 1);
        if (--i == 0) break;
      }
  }
}

/* Write GC constants of a prototype. */
static void bcwrite_kgc(BCWriteCtx *ctx, GCproto *pt)
{
  MSize i, sizekgc = pt->sizekgc;
  GCRef *kr = mref(pt->k, GCRef) - (ptrdiff_t)sizekgc;
  for (i = 0; i < sizekgc; i++, kr++) {
    GCobj *o = gcref(*kr);
    MSize tp, need = 1;
    char *p;
    /* Determine constant type and needed size. */
    if (o->gch.gct == ~LJ_TSTR) {           // 字符串
      tp = BCDUMP_KGC_STR + gco2str(o)->len;
      need = 5+gco2str(o)->len;
    } else if (o->gch.gct == ~LJ_TPROTO) {  // 子函数
      lua_assert((pt->flags & PROTO_CHILD));
      tp = BCDUMP_KGC_CHILD;
#if LJ_HASFFI
    } else if (o->gch.gct == ~LJ_TCDATA) {  
      CTypeID id = gco2cd(o)->ctypeid;
      need = 1+4*5;
      if (id == CTID_INT64) {               // Int64
        tp = BCDUMP_KGC_I64;
      } else if (id == CTID_UINT64) {       // Uint64
        tp = BCDUMP_KGC_U64;
      } else {
	lua_assert(id == CTID_COMPLEX_DOUBLE);    // double
        tp = BCDUMP_KGC_COMPLEX;
      }
#endif
    } else {
      lua_assert(o->gch.gct == ~LJ_TTAB);
      tp = BCDUMP_KGC_TAB;                  // table
      need = 1+2*5;
    }
    /* Write constant type. */
    p = lj_buf_more(&ctx->sb, need);
    p = lj_strfmt_wuleb128(p, tp);
    /* Write constant data (if any). */
    if (tp >= BCDUMP_KGC_STR) {
      p = lj_buf_wmem(p, strdata(gco2str(o)), gco2str(o)->len);
    } else if (tp == BCDUMP_KGC_TAB) {
      bcwrite_ktab(ctx, p, gco2tab(o));
      continue;
#if LJ_HASFFI
    } else if (tp != BCDUMP_KGC_CHILD) {
      cTValue *q = (TValue *)cdataptr(gco2cd(o));
      p = lj_strfmt_wuleb128(p, q[0].u32.lo);
      p = lj_strfmt_wuleb128(p, q[0].u32.hi);
      if (tp == BCDUMP_KGC_COMPLEX) {
        p = lj_strfmt_wuleb128(p, q[1].u32.lo);
        p = lj_strfmt_wuleb128(p, q[1].u32.hi);
      }
#endif
    }
    setsbufP(&ctx->sb, p);
  }
}

/* Write number constants of a prototype. */
static void bcwrite_knum(BCWriteCtx *ctx, GCproto *pt)
{
  MSize i, sizekn = pt->sizekn;
  cTValue *o = mref(pt->k, TValue);
  char *p = lj_buf_more(&ctx->sb, 10*sizekn);
  for (i = 0; i < sizekn; i++, o++) {
    int32_t k;
    if (tvisint(o)) {
      k = intV(o);
      goto save_int;
    } else {
      /* Write a 33 bit ULEB128 for the int (lsb=0) or loword (lsb=1). */
      // 数值常量分为lo低部分与hi高部分
      // 注意lo的类型为uleb128_33，它是一个33位版本的uleb128
      // 即判断第一个字节后面是否还包含后续数据时，首先判断第33位是否置1。它的定义如下：
      if (!LJ_DUALNUM) {  /* Narrow number constants to integers. */
        lua_Number num = numV(o);
        k = lj_num2int(num);
        if (num == (lua_Number)k) {  /* -0 is never a constant. */
        save_int:
          p = lj_strfmt_wuleb128(p, 2*(uint32_t)k | ((uint32_t)k&0x80000000u));
          if (k < 0)
            p[-1] = (p[-1] & 7) | ((k>>27) & 0x18);
          continue;
        }
      }
      p = lj_strfmt_wuleb128(p, 1+(2*o->u32.lo | (o->u32.lo & 0x80000000u)));
      if (o->u32.lo >= 0x80000000u)
        p[-1] = (p[-1] & 7) | ((o->u32.lo>>27) & 0x18);
      p = lj_strfmt_wuleb128(p, o->u32.hi);
    }
  }
  setsbufP(&ctx->sb, p);
}

/* Write bytecode instructions. */
static char *bcwrite_bytecode(BCWriteCtx *ctx, char *p, GCproto *pt)
{
  MSize nbc = pt->sizebc-1;  /* Omit the [JI]FUNC* header. */
#if LJ_HASJIT
  uint8_t *q = (uint8_t *)p;
#endif
  p = lj_buf_wmem(p, proto_bc(pt)+1, nbc*(MSize)sizeof(BCIns));
  UNUSED(ctx);
#if LJ_HASJIT
  /* Unpatch modified bytecode containing ILOOP/JLOOP etc. */
  if ((pt->flags & PROTO_ILOOP) || pt->trace) {
    jit_State *J = L2J(sbufL(&ctx->sb));
    MSize i;
    for (i = 0; i < nbc; i++, q += sizeof(BCIns)) {
      BCOp op = (BCOp)q[LJ_ENDIAN_SELECT(0, 3)];
      if (op == BC_IFORL || op == BC_IITERL || op == BC_ILOOP ||
	  op == BC_JFORI) {
	q[LJ_ENDIAN_SELECT(0, 3)] = (uint8_t)(op-BC_IFORL+BC_FORL);
      } else if (op == BC_JFORL || op == BC_JITERL || op == BC_JLOOP) {
	BCReg rd = q[LJ_ENDIAN_SELECT(2, 1)] + (q[LJ_ENDIAN_SELECT(3, 0)] << 8);
	memcpy(q, &traceref(J, rd)->startins, 4);
      }
    }
  }
#endif
  return p;
}

/* Write prototype. */
static void bcwrite_proto(BCWriteCtx *ctx, GCproto *pt)
{
  MSize sizedbg = 0;
  char *p;

  /* Recursively write children of prototype. */
  // 递归 write: 先写子Proto
  // PROTO_CHILD 标识当前Proto拥有“子函数”
  // 当flags字段的PROTO_CHILD标志位被置位，则表示当前层的Proto是（文件中）上一层Proto的Closure
  if ((pt->flags & PROTO_CHILD)) {
    ptrdiff_t i, n = pt->sizekgc;
    GCRef *kr = mref(pt->k, GCRef) - 1;
    for (i = 0; i < n; i++, kr--) {
      GCobj *o = gcref(*kr);
      if (o->gch.gct == ~LJ_TPROTO)
	bcwrite_proto(ctx, gco2pt(o));
    }
  }

  /* Start writing the prototype info to a buffer. */
  p = lj_buf_need(&ctx->sb,
		  5+4+6*5+(pt->sizebc-1)*(MSize)sizeof(BCIns)+pt->sizeuv*2);

  // size字段是标识了从当前字段开始，整个Proto结构体的大小
  p += 5;  /* Leave room for final size. */

  // PROTO_VARARG 标识了当前Proto是否有可变参数列表
  // PROTO_FII 标识当前Proto是否有通过FFI扩展调用系统的功能函数
  /* Write prototype header. */
  *p++ = (pt->flags & (PROTO_CHILD|PROTO_VARARG|PROTO_FFI));
  *p++ = pt->numparams;     // 表示当前Proto有几个参数
  *p++ = pt->framesize;     // 标识了Proto使用的栈大小
  *p++ = pt->sizeuv;        // UpValue个数
  p = lj_strfmt_wuleb128(p, pt->sizekgc);   // 复合常数
  p = lj_strfmt_wuleb128(p, pt->sizekn);    // 数值常数
  p = lj_strfmt_wuleb128(p, pt->sizebc-1);  // 指令条数

  if (!ctx->strip) {
    if (proto_lineinfo(pt))
      sizedbg = pt->sizept - (MSize)((char *)proto_lineinfo(pt) - (char *)pt);
    p = lj_strfmt_wuleb128(p, sizedbg); // 字段指明后面DebugInfo结构体占用的字节大小
    if (sizedbg) {
      p = lj_strfmt_wuleb128(p, pt->firstline); // 指明当前Proto在源文件中的起始行
      p = lj_strfmt_wuleb128(p, pt->numline);   // 字段指明当前Proto在源文件中所占的行数
    }
  }

  /* Write bytecode instructions and upvalue refs. */
  // 指令Instruction数组，每条指令长度与Luac一样，占用32位
  p = bcwrite_bytecode(ctx, p, pt);

  // UpValue，每个UpValue信息占用16位
  p = lj_buf_wmem(p, proto_uv(pt), pt->sizeuv*2);
  setsbufP(&ctx->sb, p);
  
  /* Write constants. */
  // 复合常数，保存的常量信息比较丰富，它可以保存字符串、整型、浮点型、TAB表结构等信息
  bcwrite_kgc(ctx, pt);

  // 数值常数，
  bcwrite_knum(ctx, pt);

  /* Write debug info, if not stripped. */
  if (sizedbg) {
    p = lj_buf_more(&ctx->sb, sizedbg);
    p = lj_buf_wmem(p, proto_lineinfo(pt), sizedbg);
    setsbufP(&ctx->sb, p);
  }

  /* Pass buffer to writer function. */
  if (ctx->status == 0) {
    MSize n = sbuflen(&ctx->sb) - 5;
    MSize nn = (lj_fls(n)+8)*9 >> 6;
    char *q = sbufB(&ctx->sb) + (5 - nn);
    p = lj_strfmt_wuleb128(q, n);  /* Fill in final size. */
    lua_assert(p == sbufB(&ctx->sb) + 5);
    ctx->status = ctx->wfunc(sbufL(&ctx->sb), q, nn+n, ctx->wdata);
  }
}

/* Write header of bytecode dump. */
static void bcwrite_header(BCWriteCtx *ctx)
{
  GCstr *chunkname = proto_chunkname(ctx->pt);
  const char *name = strdata(chunkname);
  MSize len = chunkname->len;
  char *p = lj_buf_need(&ctx->sb, 5+5+len);
  
  // 第一个signature字段是Luajit文件的Magic Number，它占用三个字节
  // 即Luajit字节码文件的头三个字节必须为“\x1bLJ”
  *p++ = BCDUMP_HEAD1;
  *p++ = BCDUMP_HEAD2;
  *p++ = BCDUMP_HEAD3;

  // BCDUMP_VERSION字段为Luajit的版本号，目前它的值为2
  *p++ = BCDUMP_VERSION;

  // 第三个字段flags描述了该文件的一组标志位集合
  // BCDUMP_F_BE 标识了该Luajit文件是采用大端字节序还是小端字节序 BE for BIG ENDIAN
  // BCDUMP_F_STRIP 标识该Luajit文件是否去除了调试信息
  // BCDUMP_F_FFI 标识是否包含FFI信息
  *p++ = (ctx->strip ? BCDUMP_F_STRIP : 0) +
	 LJ_BE*BCDUMP_F_BE +
	 ((ctx->pt->flags & PROTO_FFI) ? BCDUMP_F_FFI : 0) +
	 LJ_FR2*BCDUMP_F_FR2;

  // flags字段使用的数据类型为uleb128
  // uleb128是一种常见的压缩形式的数据存储方式
  // 它最长采用5个字节表示数据的大小，最少采用1个字节表示数据的大小
  // 具体采用的位数，可以通过判断每字节的最高位是否为1，为1则使用下一字节的数据
  if (!ctx->strip) {
    p = lj_strfmt_wuleb128(p, len); // length是uleb128表示的字段串长度
    p = lj_buf_wmem(p, name, len);  // chunkname则是存放了length长度的字段串内容，它表示当前Luajit文件的源文件名
  }

  ctx->status = ctx->wfunc(sbufL(&ctx->sb), sbufB(&ctx->sb),
			   (MSize)(p - sbufB(&ctx->sb)), ctx->wdata);
}

/* Write footer of bytecode dump. */
static void bcwrite_footer(BCWriteCtx *ctx)
{
  if (ctx->status == 0) {
    uint8_t zero = 0;
    ctx->status = ctx->wfunc(sbufL(&ctx->sb), &zero, 1, ctx->wdata);
  }
}

/* Protected callback for bytecode writer. */
static TValue *cpwriter(lua_State *L, lua_CFunction dummy, void *ud)
{
  BCWriteCtx *ctx = (BCWriteCtx *)ud;
  UNUSED(L); UNUSED(dummy);
  lj_buf_need(&ctx->sb, 1024);  /* Avoids resize for most prototypes. */
  bcwrite_header(ctx);
  bcwrite_proto(ctx, ctx->pt);
  bcwrite_footer(ctx);
  return NULL;
}

/* Write bytecode for a prototype. */
int lj_bcwrite(lua_State *L, GCproto *pt, lua_Writer writer, void *data,
	      int strip)
{
  BCWriteCtx ctx;
  int status;
  ctx.pt = pt;
  ctx.wfunc = writer;
  ctx.wdata = data;
  ctx.strip = strip;
  ctx.status = 0;
  lj_buf_init(L, &ctx.sb);
  status = lj_vm_cpcall(L, NULL, &ctx, cpwriter);
  if (status == 0) status = ctx.status;
  lj_buf_free(G(sbufL(&ctx.sb)), &ctx.sb);
  return status;
}

