/* Subroutines used for expanding RISC-V builtins.
   Copyright (C) 2011-2020 Free Software Foundation, Inc.
   Contributed by Andrew Waterman (andrew@sifive.com).

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "tree.h"
#include "gimple-expr.h"
#include "memmodel.h"
#include "expmed.h"
#include "profile-count.h"
#include "optabs.h"
#include "recog.h"
#include "diagnostic-core.h"
#include "stor-layout.h"
#include "expr.h"
#include "langhooks.h"
#include "function.h"
#include "emit-rtl.h"
#include "explow.h"

/* Macros to create an enumeration identifier for a function prototype.  */
#define RISCV_FTYPE_NAME0(A) RISCV_##A##_FTYPE
#define RISCV_FTYPE_NAME1(A, B) RISCV_##A##_FTYPE_##B
#define RISCV_FTYPE_NAME2(A, B, C) RISCV_##A##_FTYPE_##B##_##C
#define RISCV_FTYPE_NAME3(A, B, C, D) RISCV_##A##_FTYPE_##B##_##C##_##D
#define RISCV_FTYPE_NAME4(A, B, C, D, E) \
  RISCV_##A##_FTYPE_##B##_##C##_##D##_##E
#define RISCV_FTYPE_NAME5(A, B, C, D, E, F) \
  RISCV_##A##_FTYPE_##B##_##C##_##D##_##E##_##F
#define RISCV_FTYPE_NAME6(A, B, C, D, E, F, G) \
  RISCV_##A##_FTYPE_##B##_##C##_##D##_##E##_##F##_##G
#define RISCV_FTYPE_NAME7(A, B, C, D, E, F, G, H) \
  RISCV_##A##_FTYPE_##B##_##C##_##D##_##E##_##F##_##G##_##H

/* Classifies the prototype of a built-in function.  */
enum riscv_function_type {
#define DEF_RISCV_FTYPE(NARGS, LIST) RISCV_FTYPE_NAME##NARGS LIST,
#include "config/riscv/riscv-ftypes.def"
#undef DEF_RISCV_FTYPE
  RISCV_MAX_FTYPE_MAX
};

/* Specifies how a built-in function should be converted into rtl.  */
enum riscv_builtin_type {
  /* The function corresponds directly to an .md pattern.  */
  RISCV_BUILTIN_DIRECT,

  /* Likewise, but with return type VOID.  */
  RISCV_BUILTIN_DIRECT_NO_TARGET
};

/* Declare an availability predicate for built-in functions.  */
#define AVAIL(NAME, COND)		\
 static unsigned int			\
 riscv_builtin_avail_##NAME (void)	\
 {					\
   return (COND);			\
 }

/* This structure describes a single built-in function.  */
struct riscv_builtin_description {
  /* The code of the main .md file instruction.  See riscv_builtin_type
     for more information.  */
  enum insn_code icode;

  /* The name of the built-in function.  */
  const char *name;

  /* Specifies how the function should be expanded.  */
  enum riscv_builtin_type builtin_type;

  /* The function's prototype.  */
  enum riscv_function_type prototype;

  /* Whether the function is available.  */
  unsigned int (*avail) (void);
};

AVAIL (hard_float, TARGET_HARD_FLOAT)
AVAIL (rvp_64, TARGET_RVP && TARGET_64BIT)
AVAIL (rvp_32, TARGET_RVP && !TARGET_64BIT)

/* Construct a riscv_builtin_description from the given arguments.

   INSN is the name of the associated instruction pattern, without the
   leading CODE_FOR_riscv_.

   NAME is the name of the function itself, without the leading
   "__builtin_riscv_".

   BUILTIN_TYPE and FUNCTION_TYPE are riscv_builtin_description fields.

   AVAIL is the name of the availability predicate, without the leading
   riscv_builtin_avail_.  */
#define RISCV_BUILTIN(INSN, NAME, BUILTIN_TYPE,	FUNCTION_TYPE, AVAIL)	\
  { CODE_FOR_riscv_ ## INSN, "__builtin_riscv_" NAME,			\
    BUILTIN_TYPE, FUNCTION_TYPE, riscv_builtin_avail_ ## AVAIL }

/* Define __builtin_riscv_<INSN>, which is a RISCV_BUILTIN_DIRECT function
   mapped to instruction CODE_FOR_riscv_<INSN>,  FUNCTION_TYPE and AVAIL
   are as for RISCV_BUILTIN.  */
#define DIRECT_BUILTIN(INSN, FUNCTION_TYPE, AVAIL)			\
  RISCV_BUILTIN (INSN, #INSN, RISCV_BUILTIN_DIRECT, FUNCTION_TYPE, AVAIL)

/* Define __builtin_riscv_<INSN>, which is a RISCV_BUILTIN_DIRECT_NO_TARGET
   function mapped to instruction CODE_FOR_riscv_<INSN>,  FUNCTION_TYPE
   and AVAIL are as for RISCV_BUILTIN.  */
#define DIRECT_NO_TARGET_BUILTIN(INSN, FUNCTION_TYPE, AVAIL)		\
  RISCV_BUILTIN (INSN, #INSN, RISCV_BUILTIN_DIRECT_NO_TARGET,		\
		FUNCTION_TYPE, AVAIL)

/* [RVP] A trivial way to define __builtin_riscv_<INSN> for both 32bit and 
   64bit target if you are using <X:mode>, since several insn patterns is defined as 
   'riscv_insn_<xlen>'. */
#define RVP_DIRECT_BUILTIN_GPR(INSN, FUNCTION_TYPE)	\
  RISCV_BUILTIN (INSN ## si, #INSN, RISCV_BUILTIN_DIRECT, FUNCTION_TYPE, rvp_32),   \
  RISCV_BUILTIN (INSN ## di, #INSN, RISCV_BUILTIN_DIRECT, FUNCTION_TYPE, rvp_64)

#define RVP_RISCV_BUILTIN(INSN, NAME,	FUNCTION_TYPE, AVAIL)	\
  { CODE_FOR_ ## INSN, "__builtin_riscv_" # NAME,			\
    RISCV_BUILTIN_DIRECT, FUNCTION_TYPE, riscv_builtin_avail_ ## AVAIL }

#define RVP_DIRECT_BUILTIN(ICODE, ICODE64, INSN, FUNCTION_TYPE)	\
  RVP_RISCV_BUILTIN (ICODE, #INSN, FUNCTION_TYPE, rvp_32),   \
  RVP_RISCV_BUILTIN (ICODE64, #INSN, FUNCTION_TYPE, rvp_64)

#define RVP_ICODE_BUILTIN(ICODE, INSN, FUNCTION_TYPE, AVAIL)			\
  RISCV_BUILTIN (ICODE, #INSN, RISCV_BUILTIN_DIRECT, FUNCTION_TYPE, AVAIL)

/* Helper type node for target-specific types support 
   [FIXME] if you find a better way to define insn patterns with 
   arguments intxlen_t */
tree uint_xlen_node;
tree int_xlen_node;

/* Argument types.  */
#define RISCV_ATYPE_VOID void_type_node
#define RISCV_ATYPE_SI intSI_type_node
#define RISCV_ATYPE_USI unsigned_intSI_type_node
#define RISCV_ATYPE_ULONG long_unsigned_type_node
#define RISCV_ATYPE_LONG long_integer_type_node
#define RISCV_ATYPE_LLONG long_long_integer_type_node
#define RISCV_ATYPE_ULLONG  long_long_unsigned_type_node
#define RISCV_ATYPE_PSI build_pointer_type (integer_type_node)
#define RISCV_ATYPE_PUSI build_pointer_type (unsigned_type_node)
#define RISCV_ATYPE_PLLONG build_pointer_type (long_long_integer_type_node)
#define RISCV_ATYPE_PULLONG build_pointer_type (long_long_unsigned_type_node)
#define RISCV_ATYPE_TI intTI_type_node
#define RISCV_ATYPE_UTI unsigned_intTI_type_node
#define RISCV_ATYPE_V4QI build_vector_type (intQI_type_node, 4)
#define RISCV_ATYPE_UV4QI build_vector_type (unsigned_intQI_type_node, 4)
#define RISCV_ATYPE_V8QI build_vector_type (intQI_type_node, 8)
#define RISCV_ATYPE_UV8QI build_vector_type (unsigned_intQI_type_node, 8)
#define RISCV_ATYPE_V2HI build_vector_type (intHI_type_node, 2)
#define RISCV_ATYPE_UV2HI build_vector_type (unsigned_intHI_type_node, 2)
#define RISCV_ATYPE_V4HI build_vector_type (intHI_type_node, 4)
#define RISCV_ATYPE_UV4HI build_vector_type (unsigned_intHI_type_node, 4)
#define RISCV_ATYPE_V2SI build_vector_type (intSI_type_node, 2)
#define RISCV_ATYPE_UV2SI build_vector_type (unsigned_intSI_type_node, 2)
#define RISCV_ATYPE_V4SI build_vector_type (intSI_type_node, 4)
#define RISCV_ATYPE_UV4SI build_vector_type (unsigned_intSI_type_node, 4)
#define RISCV_ATYPE_V8HI build_vector_type (intHI_type_node, 8)
#define RISCV_ATYPE_UV8HI build_vector_type (unsigned_intHI_type_node, 8)

#define RISCV_ATYPE_DI intDI_type_node
#define RISCV_ATYPE_UDI unsigned_intDI_type_node
#define RISCV_ATYPE_IXLEN  int_xlen_node
#define RISCV_ATYPE_UIXLEN uint_xlen_node

/* RISCV_FTYPE_ATYPESN takes N RISCV_FTYPES-like type codes and lists
   their associated RISCV_ATYPEs.  */
#define RISCV_FTYPE_ATYPES0(A) \
  RISCV_ATYPE_##A
#define RISCV_FTYPE_ATYPES1(A, B) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B
#define RISCV_FTYPE_ATYPES2(A, B, C) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B, RISCV_ATYPE_##C
#define RISCV_FTYPE_ATYPES3(A, B, C, D) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B, RISCV_ATYPE_##C, RISCV_ATYPE_##D
#define RISCV_FTYPE_ATYPES4(A, B, C, D, E) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B, RISCV_ATYPE_##C, RISCV_ATYPE_##D, \
  RISCV_ATYPE_##E
#define RISCV_FTYPE_ATYPES5(A, B, C, D, E, F) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B, RISCV_ATYPE_##C, RISCV_ATYPE_##D, \
  RISCV_ATYPE_##E, RISCV_ATYPE_##F
#define RISCV_FTYPE_ATYPES6(A, B, C, D, E, F, G) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B, RISCV_ATYPE_##C, RISCV_ATYPE_##D, \
  RISCV_ATYPE_##E, RISCV_ATYPE_##F, RISCV_ATYPE_##G
#define RISCV_FTYPE_ATYPES7(A, B, C, D, E, F, G, H) \
  RISCV_ATYPE_##A, RISCV_ATYPE_##B, RISCV_ATYPE_##C, RISCV_ATYPE_##D, \
  RISCV_ATYPE_##E, RISCV_ATYPE_##F, RISCV_ATYPE_##G, RISCV_ATYPE_##H

static const struct riscv_builtin_description riscv_builtins[] = {
    /* DSP Extension: SIMD 16bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (addv2hi3, addv4hi3, add16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (addv2hi3, addv2hi3, v_uadd16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (addv2hi3, addv2hi3, v_sadd16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (addv4hi3, addv4hi3, v64_uadd16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (addv4hi3, addv4hi3, v64_sadd16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (raddv2hi3, raddv4hi3, radd16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (raddv2hi3, raddv2hi3, v_radd16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (raddv4hi3, raddv4hi3, v64_radd16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (uraddv2hi3, uraddv4hi3, uradd16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uraddv2hi3, uraddv2hi3, v_uradd16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (uraddv4hi3, uraddv4hi3, v64_uradd16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (kaddv2hi3, kaddv4hi3, kadd16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kaddv2hi3, kaddv2hi3, v_kadd16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kaddv4hi3, kaddv4hi3, v64_kadd16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ukaddv2hi3, ukaddv4hi3, ukadd16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukaddv2hi3, ukaddv2hi3, v_ukadd16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ukaddv4hi3, ukaddv4hi3, v64_ukadd16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (subv2hi3, subv4hi3, sub16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (subv2hi3, subv2hi3, v_usub16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (subv2hi3, subv2hi3, v_ssub16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (subv4hi3, subv4hi3, v64_usub16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (subv4hi3, subv4hi3, v64_ssub16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (rsubv2hi3, rsubv4hi3, rsub16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rsubv2hi3, rsubv2hi3, v_rsub16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (rsubv4hi3, rsubv4hi3, v64_rsub16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ursubv2hi3, ursubv4hi3, ursub16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ursubv2hi3, ursubv2hi3, v_ursub16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ursubv4hi3, ursubv4hi3, v64_ursub16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (ksubv2hi3, ksubv4hi3, ksub16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ksubv2hi3, ksubv2hi3, v_ksub16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (ksubv4hi3, ksubv4hi3, v64_ksub16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (uksubv2hi3, uksubv4hi3, uksub16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uksubv2hi3, uksubv2hi3, v_uksub16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (uksubv4hi3, uksubv4hi3, v64_uksub16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (crasv2hi, cras16_64, cras16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (crasv2hi, crasv2hi, v_ucras16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (cras16_64, cras16_64, v64_ucras16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (crasv2hi, crasv2hi, v_scras16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (cras16_64, cras16_64, v64_scras16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (rcrasv2hi, rcras16_64, rcras16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rcrasv2hi, rcrasv2hi, v_rcras16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (rcras16_64, rcras16_64, v64_rcras16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (urcrasv2hi, urcras16_64, urcras16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urcrasv2hi, urcrasv2hi, v_urcras16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (urcras16_64, urcras16_64, v64_urcras16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (kcrasv2hi, kcras16_64, kcras16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kcrasv2hi, kcrasv2hi, v_kcras16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kcras16_64, kcras16_64, v64_kcras16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ukcrasv2hi, ukcras16_64, ukcras16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukcrasv2hi, ukcrasv2hi, v_ukcras16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ukcras16_64, ukcras16_64, v64_ukcras16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (crsav2hi, crsa16_64, crsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (crsav2hi, crsav2hi, v_ucrsa16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (crsa16_64, crsa16_64, v64_ucrsa16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (crsav2hi, crsav2hi, v_scrsa16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (crsa16_64, crsa16_64, v64_scrsa16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (rcrsav2hi, rcrsa16_64, rcrsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rcrsav2hi, rcrsav2hi, v_rcrsa16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (rcrsa16_64, rcrsa16_64, v64_rcrsa16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (urcrsav2hi, urcrsa16_64, urcrsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urcrsav2hi, urcrsav2hi, v_urcrsa16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (urcrsa16_64, urcrsa16_64, v64_urcrsa16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (kcrsav2hi, kcrsa16_64, kcrsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kcrsav2hi, kcrsav2hi, v_kcrsa16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kcrsa16_64, kcrsa16_64, v64_kcrsa16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ukcrsav2hi, ukcrsa16_64, ukcrsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukcrsav2hi, ukcrsav2hi, v_ukcrsa16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ukcrsa16_64, ukcrsa16_64, v64_ukcrsa16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (stasv2hi, stas16_64, stas16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (stasv2hi, stasv2hi, v_ustas16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (stas16_64, stas16_64, v64_ustas16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (stasv2hi, stasv2hi, v_sstas16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (stas16_64, stas16_64, v64_sstas16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (rstasv2hi, rstas16_64, rstas16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rstasv2hi, rstasv2hi, v_rstas16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (rstas16_64, rstas16_64, v64_rstas16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (urstasv2hi, urstas16_64, urstas16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urstasv2hi, urstasv2hi, v_urstas16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (urstas16_64, urstas16_64, v64_urstas16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (kstasv2hi, kstas16_64, kstas16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kstasv2hi, kstasv2hi, v_kstas16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kstas16_64, kstas16_64, v64_kstas16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ukstasv2hi, ukstas16_64, ukstas16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukstasv2hi, ukstasv2hi, v_ukstas16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ukstas16_64, ukstas16_64, v64_ukstas16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (stsav2hi, stsa16_64, stsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (stsav2hi, stsav2hi, v_ustsa16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (stsa16_64, stsa16_64, v64_ustsa16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (stsav2hi, stsav2hi, v_sstsa16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (stsa16_64, stsa16_64, v64_sstsa16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (rstsav2hi, rstsa16_64, rstsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rstsav2hi, rstsav2hi, v_rstsa16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (rstsa16_64, rstsa16_64, v64_rstsa16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (urstsav2hi, urstsa16_64, urstsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urstsav2hi, urstsav2hi, v_urstsa16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (urstsa16_64, urstsa16_64, v64_urstsa16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (kstsav2hi, kstsa16_64, kstsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kstsav2hi, kstsav2hi, v_kstsa16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kstsa16_64, kstsa16_64, v64_kstsa16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ukstsav2hi, ukstsa16_64, ukstsa16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukstsav2hi, ukstsav2hi, v_ukstsa16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ukstsa16_64, ukstsa16_64, v64_ukstsa16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  /* DSP Extension: SIMD 8bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (addv4qi3, addv8qi3, add8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (addv4qi3, addv4qi3, v_uadd8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (addv4qi3, addv4qi3, v_sadd8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (addv8qi3, addv8qi3, v64_uadd8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (addv8qi3, addv8qi3, v64_sadd8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (raddv4qi3, raddv8qi3, radd8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (raddv4qi3, raddv4qi3, v_radd8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (raddv8qi3, raddv8qi3, v64_radd8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (uraddv4qi3, uraddv8qi3, uradd8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uraddv4qi3, uraddv4qi3, v_uradd8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (uraddv8qi3, uraddv8qi3, v64_uradd8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_RISCV_BUILTIN (kaddv8qi3, kadd8, RISCV_ULONG_FTYPE_ULONG_ULONG, rvp_64),
  RVP_RISCV_BUILTIN (kaddv4qi3, v_kadd8, RISCV_V4QI_FTYPE_V4QI_V4QI, rvp_32),
  RVP_RISCV_BUILTIN (kaddv8qi3, v64_kadd8, RISCV_V8QI_FTYPE_V8QI_V8QI, rvp_64),
  RVP_DIRECT_BUILTIN (ukaddv4qi3, ukaddv8qi3, ukadd8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukaddv4qi3, ukaddv4qi3, v_ukadd8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (ukaddv8qi3, ukaddv8qi3, v64_ukadd8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (subv4qi3, subv8qi3, sub8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (subv4qi3, subv4qi3, v_usub8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (subv4qi3, subv4qi3, v_ssub8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (subv8qi3, subv8qi3, v64_usub8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (subv8qi3, subv8qi3, v64_ssub8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (rsubv4qi3, rsubv8qi3, rsub8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rsubv4qi3, rsubv4qi3, v_rsub8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (rsubv8qi3, rsubv8qi3, v64_rsub8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (ursubv4qi3, ursubv8qi3, ursub8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ursubv4qi3, ursubv4qi3, v_ursub8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (ursubv8qi3, ursubv8qi3, v64_ursub8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (ksubv4qi3, ksubv8qi3, ksub8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ksubv4qi3, ksubv4qi3, v_ksub8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (ksubv8qi3, ksubv8qi3, v64_ksub8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (uksubv4qi3, uksubv8qi3, uksub8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uksubv4qi3, uksubv4qi3, v_uksub8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (uksubv8qi3, uksubv8qi3, v64_uksub8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  /* DSP Extension: SIMD 16bit Shift.  */
  RVP_DIRECT_BUILTIN (ashrv2hi3, ashrv4hi3, sra16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ashrv2hi3, ashrv2hi3, v_sra16,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (ashrv4hi3, ashrv4hi3, v64_sra16,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  RVP_DIRECT_BUILTIN (sra16_roundv2hi, sra16_roundv4hi, sra16_u,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sra16_roundv2hi, sra16_roundv2hi, v_sra16_u,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (sra16_roundv4hi, sra16_roundv4hi, v64_sra16_u,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  RVP_DIRECT_BUILTIN (lshrv2hi3, lshrv4hi3, srl16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (lshrv2hi3, lshrv2hi3, v_srl16,
		      RISCV_UV2HI_FTYPE_UV2HI_ULONG),
  RVP_DIRECT_BUILTIN (lshrv4hi3, lshrv4hi3, v64_srl16,
		      RISCV_UV4HI_FTYPE_UV4HI_ULONG),
  RVP_DIRECT_BUILTIN (srl16_roundv2hi, srl16_roundv4hi, srl16_u,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (srl16_roundv2hi, srl16_roundv2hi, v_srl16_u,
		      RISCV_UV2HI_FTYPE_UV2HI_ULONG),
  RVP_DIRECT_BUILTIN (srl16_roundv4hi, srl16_roundv4hi, v64_srl16_u,
		      RISCV_UV4HI_FTYPE_UV4HI_ULONG),
  RVP_DIRECT_BUILTIN (ashlv2hi3, ashlv4hi3, sll16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ashlv2hi3, ashlv2hi3, v_sll16,
		      RISCV_UV2HI_FTYPE_UV2HI_ULONG),
  RVP_DIRECT_BUILTIN (ashlv4hi3, ashlv4hi3, v64_sll16,
		      RISCV_UV4HI_FTYPE_UV4HI_ULONG),
  RVP_DIRECT_BUILTIN (kslli16v2hi, kslli16v4hi, ksll16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kslli16v2hi, kslli16v2hi, v_ksll16,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (kslli16v4hi, kslli16v4hi, v64_ksll16,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  RVP_DIRECT_BUILTIN (kslrav2hisi, kslrav4hidi, kslra16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kslrav2hisi, kslrav2hisi, v_kslra16,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (kslrav4hidi, kslrav4hidi, v64_kslra16,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  RVP_DIRECT_BUILTIN (kslrav2hisi_round, kslrav4hidi_round, kslra16_u,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kslrav2hisi_round, kslrav2hisi_round, v_kslra16_u,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (kslrav4hidi_round, kslrav4hidi_round, v64_kslra16_u,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  /* DSP Extension: SIMD 8bit Shift.  */
  RVP_DIRECT_BUILTIN (ashrv4qi3, ashrv8qi3, sra8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ashrv4qi3, ashrv4qi3, v_sra8,
		      RISCV_V4QI_FTYPE_V4QI_ULONG),
  RVP_DIRECT_BUILTIN (ashrv8qi3, ashrv8qi3, v64_sra8,
		      RISCV_V8QI_FTYPE_V8QI_ULONG),
  RVP_DIRECT_BUILTIN (sra8_roundv4qi, sra8_roundv8qi, sra8_u,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sra8_roundv4qi, sra8_roundv4qi, v_sra8_u,
		      RISCV_V4QI_FTYPE_V4QI_ULONG),
  RVP_DIRECT_BUILTIN (sra8_roundv8qi, sra8_roundv8qi, v64_sra8_u,
		      RISCV_V8QI_FTYPE_V8QI_ULONG),
  RVP_DIRECT_BUILTIN (lshrv4qi3, lshrv8qi3, srl8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (lshrv4qi3, lshrv4qi3, v_srl8,
		      RISCV_UV4QI_FTYPE_UV4QI_ULONG),
  RVP_DIRECT_BUILTIN (lshrv8qi3, lshrv8qi3, v64_srl8,
		      RISCV_UV8QI_FTYPE_UV8QI_ULONG),
  RVP_DIRECT_BUILTIN (srl8_roundv4qi, srl8_roundv8qi, srl8_u,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (srl8_roundv4qi, srl8_roundv4qi, v_srl8_u,
		      RISCV_UV4QI_FTYPE_UV4QI_ULONG),
  RVP_DIRECT_BUILTIN (srl8_roundv8qi, srl8_roundv8qi, v64_srl8_u,
		      RISCV_UV8QI_FTYPE_UV8QI_ULONG),
  RVP_DIRECT_BUILTIN (ashlv4qi3, ashlv8qi3, sll8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ashlv4qi3, ashlv4qi3, v_sll8,
		      RISCV_UV4QI_FTYPE_UV4QI_ULONG),
  RVP_DIRECT_BUILTIN (ashlv8qi3, ashlv8qi3, v64_sll8,
		      RISCV_UV8QI_FTYPE_UV8QI_ULONG),
  RVP_DIRECT_BUILTIN (kslli8v4qisi, kslli8v8qidi, ksll8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kslli8v4qisi, kslli8v4qisi, v_ksll8,
		      RISCV_V4QI_FTYPE_V4QI_ULONG),
  RVP_DIRECT_BUILTIN (kslli8v8qidi, kslli8v8qidi, v64_ksll8,
		      RISCV_V8QI_FTYPE_V8QI_ULONG),
  RVP_DIRECT_BUILTIN (kslrav4qisi, kslrav8qidi, kslra8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kslrav4qisi, kslrav4qisi, v_kslra8,
		      RISCV_V4QI_FTYPE_V4QI_USI),
  RVP_DIRECT_BUILTIN (kslrav8qidi, kslrav8qidi, v64_kslra8,
		      RISCV_V8QI_FTYPE_V8QI_USI),
  RVP_DIRECT_BUILTIN (kslrav4qisi_round, kslrav8qidi_round, kslra8_u,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (kslrav4qisi_round, kslrav4qisi_round, v_kslra8_u,
		      RISCV_V4QI_FTYPE_V4QI_USI),
  RVP_DIRECT_BUILTIN (kslrav8qidi_round, kslrav8qidi_round, v64_kslra8_u,
		      RISCV_V8QI_FTYPE_V8QI_USI),
  /* DSP Extension: SIMD 16bit Compare.  */
  RVP_DIRECT_BUILTIN (cmpeqv2hi, cmpeqv4hi, cmpeq16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (cmpeqv2hi, cmpeqv2hi, v_scmpeq16,
		      RISCV_UV2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (cmpeqv2hi, cmpeqv2hi, v_ucmpeq16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (cmpeqv4hi, cmpeqv4hi, v64_scmpeq16,
		      RISCV_UV4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (cmpeqv4hi, cmpeqv4hi, v64_ucmpeq16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (scmpltv2hi, scmpltv4hi, scmplt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (scmpltv2hi, scmpltv2hi, v_scmplt16,
		      RISCV_UV2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (scmpltv4hi, scmpltv4hi, v64_scmplt16,
		      RISCV_UV4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (scmplev2hi, scmplev4hi, scmple16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (scmplev2hi, scmplev2hi, v_scmple16,
		      RISCV_UV2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (scmplev4hi, scmplev4hi, v64_scmple16,
		      RISCV_UV4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ucmpltv2hi, ucmpltv4hi, ucmplt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ucmpltv2hi, ucmpltv2hi, v_ucmplt16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ucmpltv4hi, ucmpltv4hi, v64_ucmplt16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (ucmplev2hi, ucmplev4hi, ucmple16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ucmplev2hi, ucmplev2hi, v_ucmple16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (ucmplev4hi, ucmplev4hi, v64_ucmple16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  /* DSP Extension: SIMD 8bit Compare.  */
  RVP_DIRECT_BUILTIN (cmpeqv4qi, cmpeqv8qi, cmpeq8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (cmpeqv4qi, cmpeqv4qi, v_scmpeq8,
		      RISCV_UV4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (cmpeqv4qi, cmpeqv4qi, v_ucmpeq8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (cmpeqv8qi, cmpeqv8qi, v64_scmpeq8,
		      RISCV_UV8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (cmpeqv8qi, cmpeqv8qi, v64_ucmpeq8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (scmpltv4qi, scmpltv8qi, scmplt8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (scmpltv4qi, scmpltv4qi, v_scmplt8,
		      RISCV_UV4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (scmpltv8qi, scmpltv8qi, v64_scmplt8,
		      RISCV_UV8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (scmplev4qi, scmplev8qi, scmple8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (scmplev4qi, scmplev4qi, v_scmple8,
		      RISCV_UV4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (scmplev8qi, scmplev8qi, v64_scmple8,
		      RISCV_UV8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (ucmpltv4qi, ucmpltv8qi, ucmplt8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ucmpltv4qi, ucmpltv8qi, v_ucmplt8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (ucmpltv8qi, ucmpltv8qi, v64_ucmplt8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (ucmplev4qi, ucmplev8qi, ucmple8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ucmplev4qi, ucmplev4qi, v_ucmple8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (ucmplev8qi, ucmplev8qi, v64_ucmple8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  /* DSP Extension: SIMD 16bit Multiply.  */
  RVP_DIRECT_BUILTIN (smul16, smul16_64, smul16,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (smul16, smul16_64, v_smul16,
		      RISCV_V2SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smulx16, smulx16_64, smulx16,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (smulx16, smulx16_64, v_smulx16,
		      RISCV_V2SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (umul16, umul16_64, umul16,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (umul16, umul16_64, v_umul16,
		      RISCV_UV2SI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (umulx16, umulx16_64, umulx16,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (umulx16, umulx16_64, v_umulx16,
		      RISCV_UV2SI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (khm16v2hi, khm16v4hi, khm16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khm16v2hi, khm16v2hi, v_khm16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (khm16v4hi, khm16v4hi, v64_khm16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (khmx16v2hi, khmx16v4hi, khmx16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khmx16v2hi, khmx16v2hi, v_khmx16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (khmx16v4hi, khmx16v4hi, v64_khmx16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  /* DSP Extension: SIMD 8bit Multiply.  */
  RVP_DIRECT_BUILTIN (smul8, smul8, smul8,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (smul8, smul8, v_smul8,
		      RISCV_V4HI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (smulx8, smulx8, smulx8,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (smulx8, smulx8, v_smulx8,
		      RISCV_V4HI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (umul8, umul8, umul8,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (umul8, umul8, v_umul8,
		      RISCV_UV4HI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (umulx8, umulx8, umulx8,
		      RISCV_ULLONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (umulx8, umulx8, v_umulx8,
		      RISCV_UV4HI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (khm8v4qi, khm8v8qi, khm8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khm8v4qi, khm8v4qi, v_khm8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (khm8v8qi, khm8v8qi, v64_khm8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (khmx8v4qi, khmx8v8qi, khmx8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khmx8v4qi, khmx8v4qi, v_khmx8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (khmx8v8qi, khmx8v8qi, v64_khmx8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  /* DSP Extension: SIMD 16bit MISC.  */
  RVP_DIRECT_BUILTIN (sminv2hi3, sminv4hi3, smin16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sminv2hi3, sminv2hi3, v_smin16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (sminv4hi3, sminv4hi3, v64_smin16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (uminv2hi3, uminv4hi3, umin16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uminv2hi3, uminv2hi3, v_umin16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (uminv4hi3, uminv4hi3, v64_umin16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (smaxv2hi3, smaxv4hi3, smax16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smaxv2hi3, smaxv2hi3, v_smax16,
		      RISCV_V2HI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smaxv4hi3, smaxv4hi3, v64_smax16,
		      RISCV_V4HI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (umaxv2hi3, umaxv4hi3, umax16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (umaxv2hi3, umaxv2hi3, v_umax16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (umaxv4hi3, umaxv4hi3, v64_umax16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (sclip16v2hi, sclip16v4hi, sclip16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sclip16v2hi, sclip16v2hi, v_sclip16,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (sclip16v4hi, sclip16v4hi, v64_sclip16,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  RVP_DIRECT_BUILTIN (uclip16v2hi, uclip16v4hi, uclip16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uclip16v2hi, uclip16v2hi, v_uclip16,
		      RISCV_V2HI_FTYPE_V2HI_ULONG),
  RVP_DIRECT_BUILTIN (uclip16v4hi, uclip16v4hi, v64_uclip16,
		      RISCV_V4HI_FTYPE_V4HI_ULONG),
  RVP_DIRECT_BUILTIN (kabsv2hi2, kabsv4hi2, kabs16,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (kabsv2hi2, kabsv2hi2, v_kabs16,
		      RISCV_V2HI_FTYPE_V2HI),
  RVP_DIRECT_BUILTIN (kabsv4hi2, kabsv4hi2, v64_kabs16,
		      RISCV_V4HI_FTYPE_V4HI),
  RVP_DIRECT_BUILTIN (clrsbv2hi2, clrsbv4hi2, clrs16,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clrsbv2hi2, clrsbv2hi2, v_clrs16,
		      RISCV_UV2HI_FTYPE_V2HI),
  RVP_DIRECT_BUILTIN (clrsbv4hi2, clrsbv4hi2, v64_clrs16,
		      RISCV_UV4HI_FTYPE_V4HI),
  RVP_DIRECT_BUILTIN (clzv2hi2, clzv4hi2, clz16,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clzv2hi2, clzv2hi2, v_clz16,
		      RISCV_UV2HI_FTYPE_UV2HI),
  RVP_DIRECT_BUILTIN (clzv4hi2, clzv4hi2, v64_clz16,
		      RISCV_UV4HI_FTYPE_UV4HI),
  RVP_DIRECT_BUILTIN (clov2hi2, clov4hi2, clo16,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clov2hi2, clov2hi2, v_clo16,
		      RISCV_UV2HI_FTYPE_UV2HI),
  RVP_DIRECT_BUILTIN (clov4hi2, clov4hi2, v64_clo16,
		      RISCV_UV4HI_FTYPE_UV4HI),
  RVP_DIRECT_BUILTIN (unspec_bswap16, unspec_bswap16_64, swap16,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (unspec_bswap16, unspec_bswap16, v_swap16,
		      RISCV_UV2HI_FTYPE_UV2HI),
  RVP_DIRECT_BUILTIN (unspec_bswap16_64, unspec_bswap16_64, v64_swap16,
		      RISCV_UV4HI_FTYPE_UV4HI),
  /* DSP Extension: SIMD 8bit MISC.  */
  RVP_DIRECT_BUILTIN (sminv4qi3, sminv8qi3, smin8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sminv4qi3, sminv4qi3, v_smin8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (sminv8qi3, sminv8qi3, v64_smin8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (uminv4qi3, uminv8qi3, umin8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uminv4qi3, uminv4qi3, v_umin8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (uminv8qi3, uminv8qi3, v64_umin8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (smaxv4qi3, smaxv8qi3, smax8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smaxv4qi3, smaxv4qi3, v_smax8,
		      RISCV_V4QI_FTYPE_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (smaxv8qi3, smaxv8qi3, v64_smax8,
		      RISCV_V8QI_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (umaxv4qi3, umaxv8qi3, umax8,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (umaxv4qi3, umaxv4qi3, v_umax8,
		      RISCV_UV4QI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (umaxv8qi3, umaxv8qi3, v64_umax8,
		      RISCV_UV8QI_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (kabsv4qi2, kabsv8qi2, kabs8,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (kabsv4qi2, kabsv4qi2, v_kabs8,
		      RISCV_V4QI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (kabsv8qi2, kabsv8qi2, v64_kabs8,
		      RISCV_V8QI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (sclip8v4qi, sclip8v8qi, sclip8,
		      RISCV_LONG_FTYPE_LONG_USI),
  RVP_DIRECT_BUILTIN (sclip8v4qi, sclip8v4qi, v_sclip8,
		      RISCV_V4QI_FTYPE_V4QI_USI),
  RVP_DIRECT_BUILTIN (sclip8v8qi, sclip8v8qi, v64_sclip8,
		      RISCV_V8QI_FTYPE_V8QI_USI),
  RVP_DIRECT_BUILTIN (uclip8v4qi, uclip8v8qi, uclip8,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (uclip8v4qi, uclip8v4qi, v_uclip8,
		      RISCV_UV4QI_FTYPE_UV4QI_USI),
  RVP_DIRECT_BUILTIN (uclip8v8qi, uclip8v8qi, v64_uclip8,
		      RISCV_UV8QI_FTYPE_UV8QI_USI),
  RVP_DIRECT_BUILTIN (clrsbv4qi2, clrsbv8qi2, clrs8,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clrsbv4qi2, clrsbv4qi2, v_clrs8,
		      RISCV_UV4QI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (clrsbv8qi2, clrsbv8qi2, v64_clrs8,
		      RISCV_UV8QI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (clzv4qi2, clzv8qi2, clz8,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clzv4qi2, clzv4qi2, v_clz8,
		      RISCV_UV4QI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (clzv8qi2, clzv8qi2, v64_clz8,
		      RISCV_UV8QI_FTYPE_UV8QI),
  RVP_DIRECT_BUILTIN (clov4qi2, clov8qi2, clo8,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clov4qi2, clov4qi2, v_clo8,
		      RISCV_UV4QI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (clov8qi2, clov8qi2, v64_clo8,
		      RISCV_UV8QI_FTYPE_UV8QI),
  RVP_DIRECT_BUILTIN (unspec_bswap8, unspec_bswap8_64, swap8,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (unspec_bswap8, unspec_bswap8, v_swap8,
		      RISCV_UV4QI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (unspec_bswap8_64, unspec_bswap8_64, v64_swap8,
		      RISCV_UV8QI_FTYPE_UV8QI),
  /* DSP Extension: 8bit Unpacking.  */
  RVP_DIRECT_BUILTIN (sunpkd810, sunpkd810_64, sunpkd810,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (sunpkd810, sunpkd810, v_sunpkd810,
		      RISCV_V2HI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (sunpkd810_64, sunpkd810_64, v64_sunpkd810,
		      RISCV_V4HI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (sunpkd820, sunpkd820_64, sunpkd820,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (sunpkd820, sunpkd820, v_sunpkd820,
		      RISCV_V2HI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (sunpkd820_64, sunpkd820_64, v64_sunpkd820,
		      RISCV_V4HI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (sunpkd830, sunpkd830_64, sunpkd830,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (sunpkd830, sunpkd830, v_sunpkd830,
		      RISCV_V2HI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (sunpkd830_64, sunpkd830_64, v64_sunpkd830,
		      RISCV_V4HI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (sunpkd831, sunpkd831_64, sunpkd831,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (sunpkd831, sunpkd831, v_sunpkd831,
		      RISCV_V2HI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (sunpkd831_64, sunpkd831_64, v64_sunpkd831,
		      RISCV_V4HI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (sunpkd832, sunpkd832_64, sunpkd832,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (sunpkd832, sunpkd832, v_sunpkd832,
		      RISCV_V2HI_FTYPE_V4QI),
  RVP_DIRECT_BUILTIN (sunpkd832_64, sunpkd832_64, v64_sunpkd832,
		      RISCV_V4HI_FTYPE_V8QI),
  RVP_DIRECT_BUILTIN (zunpkd810, zunpkd810_64, zunpkd810,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (zunpkd810, zunpkd810, v_zunpkd810,
		      RISCV_UV2HI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (zunpkd810_64, zunpkd810_64, v64_zunpkd810,
		      RISCV_UV4HI_FTYPE_UV8QI),
  RVP_DIRECT_BUILTIN (zunpkd820, zunpkd820_64, zunpkd820,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (zunpkd820, zunpkd820, v_zunpkd820,
		      RISCV_UV2HI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (zunpkd820_64, zunpkd820_64, v64_zunpkd820,
		      RISCV_UV4HI_FTYPE_UV8QI),
  RVP_DIRECT_BUILTIN (zunpkd830, zunpkd830_64, zunpkd830,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (zunpkd830, zunpkd830, v_zunpkd830,
		      RISCV_UV2HI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (zunpkd830_64, zunpkd830_64, v64_zunpkd830,
		      RISCV_UV4HI_FTYPE_UV8QI),
  RVP_DIRECT_BUILTIN (zunpkd831, zunpkd831_64, zunpkd831,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (zunpkd831, zunpkd831, v_zunpkd831,
		      RISCV_UV2HI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (zunpkd831_64, zunpkd831_64, v64_zunpkd831,
		      RISCV_UV4HI_FTYPE_UV8QI),
  RVP_DIRECT_BUILTIN (zunpkd832, zunpkd832_64, zunpkd832,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (zunpkd832, zunpkd832, v_zunpkd832,
		      RISCV_UV2HI_FTYPE_UV4QI),
  RVP_DIRECT_BUILTIN (zunpkd832_64, zunpkd832_64, v64_zunpkd832,
		      RISCV_UV4HI_FTYPE_UV8QI),
  /* DSP Extension: 16bit Packing.  */
  RVP_DIRECT_BUILTIN (pkbbv2hi, pkbb64, pkbb16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pkbbv2hi, pkbbv2hi, v_pkbb16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (pkbb64, pkbb64, v64_pkbb16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (pkbtv2hi, pkbt64, pkbt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pkbtv2hi, pkbtv2hi, v_pkbt16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (pkbt64, pkbt64, v64_pkbt16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (pktbv2hi, pktb64, pktb16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pktbv2hi, pktbv2hi, v_pktb16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (pktb64, pktb64, v64_pktb16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (pkttv2hi, pktt64, pktt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pkttv2hi, pkttv2hi, v_pktt16,
		      RISCV_UV2HI_FTYPE_UV2HI_UV2HI),
  RVP_DIRECT_BUILTIN (pktt64, pktt64, v64_pktt16,
		      RISCV_UV4HI_FTYPE_UV4HI_UV4HI),
  /* DSP Extension: Signed MSW 32x32 Multiply and ADD.  */
  RVP_DIRECT_BUILTIN (smulsi3_highpart, smulv2si3_highpart, smmul,
		      RISCV_LONG_FTYPE_LONG_LONG),
  RVP_DIRECT_BUILTIN (smulv2si3_highpart, smulv2si3_highpart, v64_smmul,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smmul_round, smmulv2si3_round, smmul_u,
		      RISCV_LONG_FTYPE_LONG_LONG),
  RVP_DIRECT_BUILTIN (smmulv2si3_round, smmulv2si3_round, v64_smmul_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmmac, kmmac_64, kmmac,
		      RISCV_LONG_FTYPE_LONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (kmmac_64, kmmac_64, v64_kmmac,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmmac_round, kmmac64_round, kmmac_u,
		      RISCV_LONG_FTYPE_LONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (kmmac64_round, kmmac64_round, v64_kmmac_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmmsb, kmmsb_64, kmmsb,
		      RISCV_LONG_FTYPE_LONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (kmmsb_64, kmmsb_64, v64_kmmsb,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmmsb_round, kmmsb64_round, kmmsb_u,
		      RISCV_LONG_FTYPE_LONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (kmmsb64_round, kmmsb64_round, v64_kmmsb_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kwmmul, kwmmul_64, kwmmul,
		      RISCV_LONG_FTYPE_LONG_LONG),
  RVP_DIRECT_BUILTIN (kwmmul_64, kwmmul_64, v64_kwmmul,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kwmmul_round, kwmmul64_round, kwmmul_u,
		      RISCV_LONG_FTYPE_LONG_LONG),
  RVP_DIRECT_BUILTIN (kwmmul64_round, kwmmul64_round, v64_kwmmul_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  /* DSP Extension: Singed MSW 32x16 Multiply and Add.  */
  RVP_DIRECT_BUILTIN (smmwb, smmwb64, smmwb,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (smmwb, smmwb, v_smmwb,
		      RISCV_LONG_FTYPE_LONG_V2HI),
  RVP_DIRECT_BUILTIN (smmwb64, smmwb64, v64_smmwb,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (smmwb_round, smmwb64_round, smmwb_u,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (smmwb_round, smmwb64_round, v_smmwb_u,
		      RISCV_LONG_FTYPE_LONG_V2HI),
  RVP_DIRECT_BUILTIN (smmwb64_round, smmwb64_round, v64_smmwb_u,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (smmwt, smmwt64, smmwt,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (smmwt, smmwt, v_smmwt,
		      RISCV_LONG_FTYPE_LONG_V2HI),
  RVP_DIRECT_BUILTIN (smmwt64, smmwt64, v64_smmwt,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (smmwt_round, smmwt64_round, smmwt_u,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (smmwt_round, smmwt_round, v_smmwt_u,
		      RISCV_LONG_FTYPE_LONG_V2HI),
  RVP_DIRECT_BUILTIN (smmwt64_round, smmwt64_round, v64_smmwt_u,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawb, kmmawb64, kmmawb,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawb, kmmawb, v_kmmawb,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawb64, kmmawb64, v64_kmmawb,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawb_round, kmmawb64_round, kmmawb_u,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawb_round, kmmawb_round, v_kmmawb_u,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawb64_round, kmmawb64_round, v64_kmmawb_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawt, kmmawt64, kmmawt,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawt, kmmawt, v_kmmawt,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawt64, kmmawt64, v64_kmmawt,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawt_round, kmmawt64_round, kmmawt_u,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawt_round, kmmawt_round, v_kmmawt_u,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawt64_round, kmmawt64_round, v64_kmmawt_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmwb2, kmmwb64, kmmwb2,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmwb2, kmmwb2, v_kmmwb2,
		      RISCV_SI_FTYPE_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmwb64, kmmwb64, v64_kmmwb2,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmwb2_round, kmmwb64_round, kmmwb2_u,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmwb2_round, kmmwb2_round, v_kmmwb2_u,
		      RISCV_SI_FTYPE_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmwb64_round, kmmwb64_round, v64_kmmwb2_u,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmwt2, kmmwt64, kmmwt2,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmwt2, kmmwt2, v_kmmwt2,
		      RISCV_SI_FTYPE_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmwt64, kmmwt64, v64_kmmwt2,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmwt2_round, kmmwt64_round, kmmwt2_u,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmwt2_round, kmmwt2_round, v_kmmwt2_u,
		      RISCV_SI_FTYPE_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmwt64_round, kmmwt64_round, v64_kmmwt2_u,
		      RISCV_V2SI_FTYPE_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawb2, kmmawb2_64, kmmawb2,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawb2, kmmawb2, v_kmmawb2,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawb2_64, kmmawb2_64, v64_kmmawb2,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawb2_round, kmmawb2_64_round, kmmawb2_u,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawb2_round, kmmawb2_round, v_kmmawb2_u,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawb2_64_round, kmmawb2_64_round, v64_kmmawb2_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawt2, kmmawt2_64, kmmawt2,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawt2, kmmawt2, v_kmmawt2,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawt2_64, kmmawt2_64, v64_kmmawt2,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  RVP_DIRECT_BUILTIN (kmmawt2_round, kmmawt2_64_round, kmmawt2_u,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmmawt2_round, kmmawt2_round, v_kmmawt2_u,
		      RISCV_SI_FTYPE_SI_SI_V2HI),
  RVP_DIRECT_BUILTIN (kmmawt2_64_round, kmmawt2_64_round, v64_kmmawt2_u,
		      RISCV_V2SI_FTYPE_V2SI_V2SI_V4HI),
  /* DSP Extension: Signed 16bit Multiply with 32bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (smbb, smbb64, smbb16,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smbb, smbb, v_smbb16,
		      RISCV_SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smbb64, smbb64, v64_smbb16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smbt, smbt64, smbt16,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smbt, smbt, v_smbt16,
		      RISCV_SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smbt64, smbt64, v64_smbt16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smtt, smtt64, smtt16,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smtt, smtt, v_smtt16,
		      RISCV_SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smtt64, smtt64, v64_smtt16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmda, kmda64, kmda,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmda, kmda, v_kmda,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmda64, kmda64, v64_kmda,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmxda, kmxda64, kmxda,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmxda, kmxda, v_kmxda,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmxda64, kmxda64, v64_kmxda,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smds, smds64, smds,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smds, smds, v_smds,
		      RISCV_SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smds, smds64, v64_smds,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smdrs, smdrs64, smdrs,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smdrs, smdrs, v_smdrs,
		      RISCV_SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smdrs, smdrs64, v64_smdrs,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smxdsv, smxds64, smxds,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smxdsv, smxdsv, v_smxds,
		      RISCV_SI_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smxds64, smxds64, v64_smxds,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmabb, kmabb64, kmabb,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmabb, kmabb, v_kmabb,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmabb64, kmabb64, v64_kmabb,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmabt, kmabt64, kmabt,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmabt, kmabt, v_kmabt,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmabt64, kmabt64, v64_kmabt,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmatt, kmatt64, kmatt,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmatt, kmatt, v_kmatt,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmatt64, kmatt64, v64_kmatt,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmada, kmada64, kmada,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmada, kmada, v_kmada,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmada64, kmada64, v64_kmada,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmaxda, kmaxda64, kmaxda,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmaxda, kmaxda, v_kmaxda,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmaxda, kmaxda64, v64_kmaxda,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmads, kmads64, kmads,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmads, kmads, v_kmads,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmads64, kmads64, v64_kmads,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmadrs, kmadrs64, kmadrs,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmadrs, kmadrs, v_kmadrs,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmadrs64, kmadrs64, v64_kmadrs,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmaxds, kmaxds64, kmaxds,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmaxds, kmaxds, v_kmaxds,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmaxds64, kmaxds64, v64_kmaxds,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmsda, kmsda64, kmsda,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmsda, kmsda, v_kmsda,
		      RISCV_SI_FTYPE_SI_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmsda64, kmsda64, v64_kmsda,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kmsxda, kmsxda64, kmsxda,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmsxda, kmsxda, v_kmsxda,
		      RISCV_SI_FTYPE_SI_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kmsxda64, kmsxda64, v64_kmsxda,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  /* DSP Extension: Signed 16bit Multiply with 64bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (smal1, smal1_64, smal,
		      RISCV_LLONG_FTYPE_LLONG_ULONG),
  RVP_DIRECT_BUILTIN (smal1, smal1, v_smal,
		      RISCV_LLONG_FTYPE_LLONG_V2HI),
  RVP_DIRECT_BUILTIN (smal1_64, smal1_64, v64_smal,
		      RISCV_LLONG_FTYPE_LLONG_V4HI),
  /* DSP Extension: Partial-SIMD MISC.  */
  RVP_DIRECT_BUILTIN (sclip32sisi, sclip32v2sidi, sclip32,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (sclip32v2sidi, sclip32v2sidi, v64_sclip32,
		      RISCV_V2SI_FTYPE_V2SI_ULONG),
  RVP_DIRECT_BUILTIN (uclip32sisi, uclip32v2sidi, uclip32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uclip32v2sidi, uclip32v2sidi, v64_uclip32,
		      RISCV_UV2SI_FTYPE_UV2SI_ULONG),
  RVP_DIRECT_BUILTIN (clrsbsi2, clrsbv2si2, clrs32,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clrsbv2si2, clrsbv2si2, v64_clrs32,
		      RISCV_UV2SI_FTYPE_V2SI),
  RVP_DIRECT_BUILTIN (clzsi2, clzv2si2, clz32,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clzv2si2, clzv2si2, v64_clz32,
		      RISCV_UV2SI_FTYPE_UV2SI),
  RVP_DIRECT_BUILTIN (closi2, clov2si2, clo32,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (clov2si2, clov2si2, v64_clo32,
		      RISCV_UV2SI_FTYPE_UV2SI),
  RVP_DIRECT_BUILTIN (pbsadsi, pbsaddi, pbsad,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pbsadsi, pbsadsi, v_pbsad,
		      RISCV_USI_FTYPE_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (pbsaddi, pbsaddi, v64_pbsad,
		      RISCV_ULONG_FTYPE_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (pbsadasi, pbsadadi, pbsada,
		      RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pbsadasi, pbsadasi, v_pbsada,
		      RISCV_USI_FTYPE_USI_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (pbsadadi, pbsadadi, v64_pbsada,
		      RISCV_ULONG_FTYPE_ULONG_UV8QI_UV8QI),
  /* DSP Extension: 8bit Multiply with 32bit Add.  */
  RVP_DIRECT_BUILTIN (smaqa, smaqa64, smaqa,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smaqa, smaqa, v_smaqa,
		      RISCV_SI_FTYPE_SI_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (smaqa64, smaqa64, v64_smaqa,
		      RISCV_V2SI_FTYPE_V2SI_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (umaqa, umaqa64, umaqa,
		      RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (umaqa, umaqa, v_umaqa,
		      RISCV_USI_FTYPE_USI_UV4QI_UV4QI),
  RVP_DIRECT_BUILTIN (umaqa64, umaqa64, v64_umaqa,
		      RISCV_UV2SI_FTYPE_UV2SI_UV8QI_UV8QI),
  RVP_DIRECT_BUILTIN (sumaqa, sumaqa64, smaqa_su,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sumaqa, sumaqa, v_smaqa_su,
		      RISCV_SI_FTYPE_SI_V4QI_V4QI),
  RVP_DIRECT_BUILTIN (sumaqa64, sumaqa64, v64_smaqa_su,
		      RISCV_V2SI_FTYPE_V2SI_V8QI_V8QI),
  /* DSP Extension: 64bit Add and Subtract.  */
  RVP_DIRECT_BUILTIN (dsp_adddi3, adddi3, sadd64,
		      RISCV_LLONG_FTYPE_LLONG_LLONG),
  RVP_DIRECT_BUILTIN (dsp_adddi3, adddi3, uadd64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULLONG),
  RVP_DIRECT_BUILTIN (radddi3, radddi3, radd64,
		      RISCV_LLONG_FTYPE_LLONG_LLONG),
  RVP_DIRECT_BUILTIN (uradddi3, uradddi3, uradd64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULLONG),
  RVP_DIRECT_BUILTIN (dsp_kadddi3, dsp_kadddi3, kadd64,
		      RISCV_LLONG_FTYPE_LLONG_LLONG),
  RVP_DIRECT_BUILTIN (dsp_ukadddi3, dsp_ukadddi3, ukadd64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULLONG),
  RVP_DIRECT_BUILTIN (subdi3, subdi3, ssub64,
		      RISCV_LLONG_FTYPE_LLONG_LLONG),
  RVP_DIRECT_BUILTIN (subdi3, subdi3, usub64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULLONG),
  RVP_DIRECT_BUILTIN (rsubdi3, rsubdi3, rsub64,
		      RISCV_LLONG_FTYPE_LLONG_LLONG),
  RVP_DIRECT_BUILTIN (ursubdi3, ursubdi3, ursub64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULLONG),
  RVP_DIRECT_BUILTIN (dsp_ksubdi3, dsp_ksubdi3, ksub64,
		      RISCV_LLONG_FTYPE_LLONG_LLONG),
  RVP_DIRECT_BUILTIN (dsp_uksubdi3, dsp_uksubdi3, uksub64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULLONG),
  /* DSP Extension: 32bit Multiply with 64bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (smar64_1, vsmar64_1, smar64,
		      RISCV_LLONG_FTYPE_LLONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (vsmar64_1, vsmar64_1, v64_smar64,
		      RISCV_LLONG_FTYPE_LLONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smsr64, vsmsr64, smsr64,
		      RISCV_LLONG_FTYPE_LLONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (vsmsr64, vsmsr64, v64_smsr64,
		      RISCV_LLONG_FTYPE_LLONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (umar64_1, vumar64_1, umar64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (vumar64_1, vumar64_1, v64_umar64,
		      RISCV_ULLONG_FTYPE_ULLONG_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (umsr64, vumsr64, umsr64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (vumsr64, vumsr64, v64_umsr64,
		      RISCV_ULLONG_FTYPE_ULLONG_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (kmar64_1, vkmar64, kmar64,
		      RISCV_LLONG_FTYPE_LLONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (vkmar64, vkmar64, v64_kmar64,
		      RISCV_LLONG_FTYPE_LLONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmsr64, vkmsr64, kmsr64,
		      RISCV_LLONG_FTYPE_LLONG_LONG_LONG),
  RVP_DIRECT_BUILTIN (vkmsr64, vkmsr64, v64_kmsr64,
		      RISCV_LLONG_FTYPE_LLONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (ukmar64_1, vukmar64, ukmar64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (vukmar64, vukmar64, v64_ukmar64,
		      RISCV_ULLONG_FTYPE_ULLONG_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (ukmsr64, vukmsr64, ukmsr64,
		      RISCV_ULLONG_FTYPE_ULLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (vukmsr64, vukmsr64, v64_ukmsr64,
		      RISCV_ULLONG_FTYPE_ULLONG_UV2SI_UV2SI),
  /* DSP Extension: Signed 16bit Multiply with 64bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (smalbb, smalbb64, smalbb,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smalbb, smalbb, v_smalbb,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smalbb64, smalbb64, v64_smalbb,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smalbt, smalbt64, smalbt,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smalbt, smalbt, v_smalbt,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smalbt64, smalbt64, v64_smalbt,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smaltt, smaltt64, smaltt,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smaltt, smaltt, v_smaltt,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smaltt64, smaltt64, v64_smaltt,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smalda1, smalda64, smalda,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smalda1, smalda1, v_smalda,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smalda64, smalda64, v64_smalda,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smalxda1, smalxda64, smalxda,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smalxda1, smalxda1, v_smalxda,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smalxda64, smalxda64, v64_smalxda,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smalds1, smalds64, smalds,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smalds1, smalds1, v_smalds,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smalds64, smalds64, v64_smalds,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smaldrs3, smaldrs64, smaldrs,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smaldrs3, smaldrs3, v_smaldrs,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smaldrs64, smaldrs64, v64_smaldrs,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smalxds1, smalxds64, smalxds,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smalxds1, smalxds1, v_smalxds,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smalxds64, smalxds64, v64_smalxds,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smslda1, smslda64, smslda,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smslda1, smslda1, v_smslda,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smslda64, smslda64, v64_smslda,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (smslxda1, smslxda64, smslxda,
		      RISCV_LLONG_FTYPE_LLONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smslxda1, smslxda1, v_smslxda,
		      RISCV_LLONG_FTYPE_LLONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (smslxda1, smslxda64, v64_smslxda,
		      RISCV_LLONG_FTYPE_LLONG_V4HI_V4HI),
  /* DSP Extension: Q15 Saturation.  */
  RVP_DIRECT_BUILTIN (kaddh, kaddh, kaddh,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (ksubh, ksubh, ksubh,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (khmbbv2hi, khmbb64, khmbb,
		      RISCV_LONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (khmbbv2hi, khmbbv2hi, v_khmbb,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (khmbbv4hi, khmbbv4hi, v64_khmbb,
		      RISCV_LONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (khmbtv2hi, khmbt64, khmbt,
		      RISCV_LONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (khmbtv2hi, khmbtv2hi, v_khmbt,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (khmbtv4hi, khmbtv4hi, v64_khmbt,
		      RISCV_LONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (khmttv2hi, khmtt64, khmtt,
		      RISCV_LONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (khmttv2hi, khmttv2hi, v_khmtt,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (khmttv4hi, khmttv4hi, v64_khmtt,
		      RISCV_LONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (ukaddh, ukaddh64, ukaddh,
		      RISCV_ULONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (uksubh, uksubh64, uksubh,
		      RISCV_ULONG_FTYPE_USI_USI),
  /* DSP Extension: Q31 Saturation.  */
  RVP_DIRECT_BUILTIN (kaddw, kaddw64, kaddw,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (ukaddw, ukaddw64, ukaddw,
		      RISCV_ULONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (ksubw, ksubw64, ksubw,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (uksubw, uksubw64, uksubw,
		      RISCV_ULONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (kdmbbv2hi, kdmbb64, kdmbb,
		      RISCV_LONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (kdmbbv2hi, kdmbbv2hi, v_kdmbb,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kdmbbv4hi, kdmbbv4hi, v64_kdmbb,
		      RISCV_LONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmbtv2hi, kdmbt64, kdmbt,
		      RISCV_LONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (kdmbtv2hi, kdmbtv2hi, v_kdmbt,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kdmbtv4hi, kdmbtv4hi, v64_kdmbt,
		      RISCV_LONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmttv2hi, kdmtt64, kdmtt,
		      RISCV_LONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (kdmttv2hi, kdmttv2hi, v_kdmtt,
		      RISCV_LONG_FTYPE_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kdmttv4hi, kdmttv4hi, v64_kdmtt,
		      RISCV_LONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kslraw, kslraw64, kslraw,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (unspec_kslrawu, unspec_kslrawu64, kslraw_u,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (kssl, kssl, ksllw,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmabb, kdmabb32, kdmabb,
		      RISCV_LONG_FTYPE_LONG_USI_USI),
  RVP_DIRECT_BUILTIN (kdmabb, kdmabb, v_kdmabb,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kdmabb64, kdmabb64, v64_kdmabb,
		      RISCV_LONG_FTYPE_LONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmabt, kdmabt32, kdmabt,
		      RISCV_LONG_FTYPE_LONG_USI_USI),
  RVP_DIRECT_BUILTIN (kdmabt, kdmabt, v_kdmabt,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kdmabt64, kdmabt64, v64_kdmabt,
		      RISCV_LONG_FTYPE_LONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmatt, kdmatt32, kdmatt,
		      RISCV_LONG_FTYPE_LONG_USI_USI),
  RVP_DIRECT_BUILTIN (kdmatt, kdmatt, v_kdmatt,
		      RISCV_LONG_FTYPE_LONG_V2HI_V2HI),
  RVP_DIRECT_BUILTIN (kdmatt64, kdmatt64, v64_kdmatt,
		      RISCV_LONG_FTYPE_LONG_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kabs, kabs, kabsw,
		      RISCV_ULONG_FTYPE_LONG),
  /* DSP Extension: 32bit Computation.  */
  RVP_DIRECT_BUILTIN (raddsi3, radddisi3, raddw,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (uraddsi3, uradddisi3, uraddw,
		      RISCV_ULONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (rsubsi3, rsubdisi3, rsubw,
		      RISCV_LONG_FTYPE_SI_SI),
  RVP_DIRECT_BUILTIN (ursubsi3, ursubdisi3, ursubw,
		      RISCV_ULONG_FTYPE_USI_USI),
  RVP_DIRECT_BUILTIN (smaxsi3, smaxsi3, maxw,
		      RISCV_LONG_FTYPE_LONG_LONG),
  RVP_DIRECT_BUILTIN (sminsi3, sminsi3, minw,
		      RISCV_LONG_FTYPE_LONG_LONG),
  /* DSP Extension: Non-SIMD MISC.  */
  RVP_DIRECT_BUILTIN (unspec_ave, unspec_avedi, ave,
		      RISCV_LONG_FTYPE_LONG_LONG),
  RVP_DIRECT_BUILTIN (sraiu, sraiu64, sra_u,
		      RISCV_LONG_FTYPE_LONG_ULONG),
  RVP_DIRECT_BUILTIN (bitrev, bitrev64, bitrev,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (wext, wext64, wext,
		      RISCV_ULONG_FTYPE_LLONG_ULONG),
  RVP_DIRECT_BUILTIN (insb, insb64, insb,
		      RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),
  /* DSP Extension: RV64 only, SIMD 32bit Add/Subtract.  */
  RVP_DIRECT_BUILTIN (addv2si3, addv2si3, add32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (addv2si3, addv2si3, v64_uadd32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (addv2si3, addv2si3, v64_sadd32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (raddv2si3, raddv2si3, radd32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (raddv2si3, raddv2si3, v64_radd32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (uraddv2si3, uraddv2si3, uradd32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uraddv2si3, uraddv2si3, v64_uradd32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (kaddv2si3, kaddv2si3, kadd32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kaddv2si3, kaddv2si3, v64_kadd32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (ukaddv2si3, ukaddv2si3, ukadd32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukaddv2si3, ukaddv2si3, v64_ukadd32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (subv2si3, subv2si3, sub32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (subv2si3, subv2si3, v64_usub32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (subv2si3, subv2si3, v64_ssub32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (rsubv2si3, rsubv2si3, rsub32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rsubv2si3, rsubv2si3, v64_rsub32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (ursubv2si3, ursubv2si3, ursub32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ursubv2si3, ursubv2si3, v64_ursub32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (ksubv2si3, ksubv2si3, ksub32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ksubv2si3, ksubv2si3, v64_ksub32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (uksubv2si3, uksubv2si3, uksub32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uksubv2si3, uksubv2si3, v64_uksub32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (crasv2si, crasv2si, cras32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (crasv2si, crasv2si, v64_ucras32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (crasv2si, crasv2si, v64_scras32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (crsav2si, crsav2si, crsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (crsav2si, crsav2si, v64_ucrsa32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (crsav2si, crsav2si, v64_scrsa32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (rcrasv2si, rcrasv2si, rcras32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rcrasv2si, rcrasv2si, v64_rcras32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (rcrsav2si, rcrsav2si, rcrsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rcrsav2si, rcrsav2si, v64_rcrsa32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (urcrasv2si, urcrasv2si, urcras32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urcrasv2si, urcrasv2si, v64_urcras32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (urcrsav2si, urcrsav2si, urcrsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urcrsav2si, urcrsav2si, v64_urcrsa32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (kcrasv2si, kcrasv2si, kcras32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kcrasv2si, kcrasv2si, v64_kcras32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kcrsav2si, kcrsav2si, kcrsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kcrsav2si, kcrsav2si, v64_kcrsa32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (ukcrasv2si, ukcrasv2si, ukcras32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukcrasv2si, ukcrasv2si, v64_ukcras32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (ukcrsav2si, ukcrsav2si, ukcrsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukcrsav2si, ukcrsav2si, v64_ukcrsa32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (stasv2si, stasv2si, stas32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (stasv2si, stasv2si, v64_ustas32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (stasv2si, stasv2si, v64_sstas32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (rstasv2si, rstasv2si, rstas32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rstasv2si, rstasv2si, v64_rstas32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (urstasv2si, urstasv2si, urstas32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urstasv2si, urstasv2si, v64_urstas32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (kstasv2si, kstasv2si, kstas32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kstasv2si, kstasv2si, v64_kstas32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (ukstasv2si, ukstasv2si, ukstas32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukstasv2si, ukstasv2si, v64_ukstas32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (stsav2si, stsav2si, stsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (stsav2si, stsav2si, v64_ustsa32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (stsav2si, stsav2si, v64_sstsa32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (rstsav2si, rstsav2si, rstsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (rstsav2si, rstsav2si, v64_rstsa32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (urstsav2si, urstsav2si, urstsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (urstsav2si, urstsav2si, v64_urstsa32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (kstsav2si, kstsav2si, kstsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kstsav2si, kstsav2si, v64_kstsa32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (ukstsav2si, ukstsav2si, ukstsa32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (ukstsav2si, ukstsav2si, v64_ukstsa32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  /* DSP Extension: RV64 only, SIMD 32bit Shift.  */
  RVP_DIRECT_BUILTIN (ashrv2si3, ashrv2si3, sra32,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (ashrv2si3, ashrv2si3, v64_sra32,
		      RISCV_V2SI_FTYPE_V2SI_USI),
  RVP_DIRECT_BUILTIN (sra32_round, sra32_round, sra32_u,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (sra32_round, sra32_round, v64_sra32_u,
		      RISCV_V2SI_FTYPE_V2SI_USI),
  RVP_DIRECT_BUILTIN (lshrv2si3, lshrv2si3, srl32,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (lshrv2si3, lshrv2si3, v64_srl32,
		      RISCV_UV2SI_FTYPE_UV2SI_USI),
  RVP_DIRECT_BUILTIN (srl32_round, srl32_round, srl32_u,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (srl32_round, srl32_round, v64_srl32_u,
		      RISCV_UV2SI_FTYPE_UV2SI_USI),
  RVP_DIRECT_BUILTIN (ashlv2si3, ashlv2si3, sll32,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (ashlv2si3, ashlv2si3, v64_sll32,
		      RISCV_UV2SI_FTYPE_UV2SI_USI),
  RVP_DIRECT_BUILTIN (ksll32, ksll32, ksll32,
		      RISCV_ULONG_FTYPE_ULONG_USI),
  RVP_DIRECT_BUILTIN (ksll32, ksll32, v64_ksll32,
		      RISCV_V2SI_FTYPE_V2SI_USI),
  RVP_DIRECT_BUILTIN (kslrav2sidi, kslrav2sidi, kslra32,
		      RISCV_ULONG_FTYPE_ULONG_SI),
  RVP_DIRECT_BUILTIN (kslrav2sidi, kslrav2sidi, v64_kslra32,
		      RISCV_V2SI_FTYPE_V2SI_SI),
  RVP_DIRECT_BUILTIN (kslrav2sidi_round, kslrav2sidi_round, kslra32_u,
		      RISCV_ULONG_FTYPE_ULONG_SI),
  RVP_DIRECT_BUILTIN (kslrav2sidi_round, kslrav2sidi_round, v64_kslra32_u,
		      RISCV_V2SI_FTYPE_V2SI_SI),
  /* DSP Extension: RV64 only, SIMD 32bit MISC.  */
  RVP_DIRECT_BUILTIN (sminv2si3, sminv2si3, smin32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (sminv2si3, sminv2si3, v64_smin32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (uminv2si3, uminv2si3, umin32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (uminv2si3, uminv2si3, v64_umin32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (smaxv2si3, smaxv2si3, smax32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smaxv2si3, smaxv2si3, v64_smax32,
		      RISCV_V2SI_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (umaxv2si3, umaxv2si3, umax32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (umaxv2si3, umaxv2si3, v64_umax32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (kabsv2si2, kabsv2si2, kabs32,
		      RISCV_ULONG_FTYPE_ULONG),
  RVP_DIRECT_BUILTIN (kabsv2si2, kabsv2si2, v64_kabs32,
		      RISCV_V2SI_FTYPE_V2SI),
  /* DSP Extension: RV64 only, SIMD Q15 Saturating.  */
  RVP_DIRECT_BUILTIN (khmbb16, khmbb16, khmbb16,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khmbb16, khmbb16, v64_khmbb16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (khmbt16, khmbt16, khmbt16,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khmbt16, khmbt16, v64_khmbt16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (khmtt16, khmtt16, khmtt16,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (khmtt16, khmtt16, v64_khmtt16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmbb16, kdmbb16, kdmbb16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmbb16, kdmbb16, v64_kdmbb16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmbt16, kdmbt16, kdmbt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmbt16, kdmbt16, v64_kdmbt16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmtt16, kdmtt16, kdmtt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmtt16, kdmtt16, v64_kdmtt16,
		      RISCV_V2SI_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmabb16, kdmabb16, kdmabb16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmabb16, kdmabb16, v64_kdmabb16,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmabt16, kdmabt16, kdmabt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmabt16, kdmabt16, v64_kdmabt16,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (kdmatt16, kdmatt16, kdmatt16,
		      RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kdmatt16, kdmatt16, v64_kdmatt16,
		      RISCV_V2SI_FTYPE_V2SI_V4HI_V4HI),
  /* DSP Extension: RV64 only, 32bit Multiply.  */
  RVP_DIRECT_BUILTIN (smbb32, smbb32, smbb32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smbb32, smbb32, v64_smbb32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smbt32, smbt32, smbt32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smbt32, smbt32, v64_smbt32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smtt32, smtt32, smtt32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smtt32, smtt32, v64_smtt32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  /* DSP Extension: RV64 only, 32bit Multiply and Add.  */
  RVP_DIRECT_BUILTIN (kmabb32, kmabb32, kmabb32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmabb32, kmabb32, v64_kmabb32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmabt32, kmabt32, kmabt32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmabt32, kmabt32, v64_kmabt32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmatt32, kmatt32, kmatt32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmatt32, kmatt32, v64_kmatt32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmda32, kmda32, kmda32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmda32, kmda32, v64_kmda32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmxda32, kmxda32, kmxda32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmxda32, kmxda32, v64_kmxda32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmada32, kmada32, kmada32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmada32, kmada32, v64_kmada32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmaxda32, kmaxda32, kmaxda32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmaxda32, kmaxda32, v64_kmaxda32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmads32, kmads32, kmads32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmads32, kmads32, v64_kmads32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmadrs32, kmadrs32, kmadrs32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmadrs32, kmadrs32, v64_kmadrs32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmaxds32, kmaxds32, kmaxds32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmaxds32, kmaxds32, v64_kmaxds32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmsda32, kmsda32, kmsda32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmsda32, kmsda32, v64_kmsda32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (kmsxda32, kmsxda32, kmsxda32,
		      RISCV_LONG_FTYPE_LONG_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (kmsxda32, kmsxda32, v64_kmsxda32,
		      RISCV_LONG_FTYPE_LONG_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smds32, smds32, smds32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smds32, smds32, v64_smds32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smdrs32, smdrs32, smdrs32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smdrs32, smdrs32, v64_smdrs32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  RVP_DIRECT_BUILTIN (smxds32, smxds32, smxds32,
		      RISCV_LONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (smxds32, smxds32, v64_smxds32,
		      RISCV_LONG_FTYPE_V2SI_V2SI),
  /* DSP Extension: RV64 only, Non-SIMD 32bit Shift.  */
  RVP_DIRECT_BUILTIN (sraiw_u, sraiw_u, sraw_u,
		      RISCV_LONG_FTYPE_SI_USI),
  /* DSP Extension: RV64 only, 32bit Packing.  */
  RVP_DIRECT_BUILTIN (pkbbv2si, pkbbv2si, pkbb32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pkbbv2si, pkbbv2si, v64_pkbb32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (pkbtv2si, pkbtv2si, pkbt32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pkbtv2si, pkbtv2si, v64_pkbt32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (pktbv2si, pktbv2si, pktb32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pktbv2si, pktbv2si, v64_pktb32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  RVP_DIRECT_BUILTIN (pkttv2si, pkttv2si, pktt32,
		      RISCV_ULONG_FTYPE_ULONG_ULONG),
  RVP_DIRECT_BUILTIN (pkttv2si, pkttv2si, v64_pktt32,
		      RISCV_UV2SI_FTYPE_UV2SI_UV2SI),
  /* DSP Extension: Other.  */
  RVP_DIRECT_BUILTIN (cmpeqv4hi, cmpeqv4hi, vec_scmpeq16,
		      RISCV_ULONG_FTYPE_V4HI_V4HI),
  RVP_DIRECT_BUILTIN (cmpeqv4hi, cmpeqv4hi, vec_ucmpeq16,
		      RISCV_ULONG_FTYPE_UV4HI_UV4HI),
  RVP_DIRECT_BUILTIN (cmpeqv8qi, cmpeqv8qi, vec_scmpeq8,
		      RISCV_ULONG_FTYPE_V8QI_V8QI),
  RVP_DIRECT_BUILTIN (cmpeqv8qi, cmpeqv8qi, vec_ucmpeq8,
		      RISCV_ULONG_FTYPE_UV8QI_UV8QI),
  
  /* DSP Extension: Overflow status manipulation.  */
  RVP_DIRECT_BUILTIN_GPR (rdov, RISCV_ULONG_FTYPE_VOID),
  RVP_DIRECT_BUILTIN_GPR (clrov, RISCV_VOID_FTYPE_VOID),
  RVP_DIRECT_BUILTIN_GPR (bpick, RISCV_ULONG_FTYPE_ULONG_ULONG_ULONG),

  DIRECT_BUILTIN (frflags, RISCV_USI_FTYPE, hard_float),
  DIRECT_NO_TARGET_BUILTIN (fsflags, RISCV_VOID_FTYPE_USI, hard_float)
};

/* Index I is the function declaration for riscv_builtins[I], or null if the
   function isn't defined on this target.  */
static GTY(()) tree riscv_builtin_decls[ARRAY_SIZE (riscv_builtins)];

/* Get the index I of the function declaration for riscv_builtin_decls[I]
   using the instruction code or return null if not defined for the target.  */
static GTY(()) int riscv_builtin_decl_index[NUM_INSN_CODES];

#define GET_BUILTIN_DECL(CODE) \
  riscv_builtin_decls[riscv_builtin_decl_index[(CODE)]]

/* Return the function type associated with function prototype TYPE.  */

static tree
riscv_build_function_type (enum riscv_function_type type)
{
  static tree types[(int) RISCV_MAX_FTYPE_MAX];

  if (types[(int) type] == NULL_TREE)
    switch (type)
      {
#define DEF_RISCV_FTYPE(NUM, ARGS)					\
  case RISCV_FTYPE_NAME##NUM ARGS:					\
    types[(int) type]							\
      = build_function_type_list (RISCV_FTYPE_ATYPES##NUM ARGS,		\
				  NULL_TREE);				\
    break;
#include "config/riscv/riscv-ftypes.def"
#undef DEF_RISCV_FTYPE
      default:
	gcc_unreachable ();
      }

  return types[(int) type];
}

/* Implement TARGET_INIT_BUILTINS.  */

void
riscv_init_builtins (void)
{
  for (size_t i = 0; i < ARRAY_SIZE (riscv_builtins); i++)
    {
      const struct riscv_builtin_description *d = &riscv_builtins[i];
      if (d->avail ())
	{
	  tree type = riscv_build_function_type (d->prototype);
	  riscv_builtin_decls[i]
	    = add_builtin_function (d->name, type, i, BUILT_IN_MD, NULL, NULL);
	  riscv_builtin_decl_index[d->icode] = i;
	}
    }
}

/* Implement TARGET_BUILTIN_DECL.  */

tree
riscv_builtin_decl (unsigned int code, bool initialize_p ATTRIBUTE_UNUSED)
{
  if (code >= ARRAY_SIZE (riscv_builtins))
    return error_mark_node;
  return riscv_builtin_decls[code];
}

/* Take argument ARGNO from EXP's argument list and convert it into
   an expand operand.  Store the operand in *OP.  In P extension, it
   helps to make conversions from vectorized mode to constant mode, e.g.
   v8qi to long */

static void
riscv_rvp_prepare_builtin_arg (struct expand_operand *op, tree exp, unsigned argno,
			   enum insn_code icode, bool has_target_p)
{
  enum machine_mode mode = insn_data[icode].operand[argno + has_target_p].mode;
  rtx arg = expand_normal (CALL_EXPR_ARG (exp, argno));
  rtx tmp_rtx = gen_reg_rtx (mode);

  if (!(*insn_data[icode].operand[argno + has_target_p].predicate) (arg, mode))
    {
      if (GET_MODE_SIZE (mode) < GET_MODE_SIZE (GET_MODE (arg)))
	{
	  tmp_rtx = simplify_gen_subreg (mode, arg, GET_MODE (arg), 0);
	  arg = tmp_rtx;
	}
      else if (VECTOR_MODE_P (mode) && SCALAR_INT_MODE_P (GET_MODE(arg)))
	{
    fprintf(stderr, "I AM HERE! \n");
	  /* Handle CONST_INT covert to CONST_VECTOR.  */
	  int nunits = GET_MODE_NUNITS (mode);
    fprintf(stderr, "nunits : %d\n", nunits);
	  int i, shift = 0;
	  rtvec v = rtvec_alloc (nunits);
	  HOST_WIDE_INT val = INTVAL (arg);
    fprintf(stderr, "HOST_WIDE_INT val = INTVAL (arg) =  %u\n", val);
	  enum machine_mode val_mode = GET_MODE_INNER (mode);
	  int shift_acc = GET_MODE_BITSIZE (val_mode);
    fprintf(stderr, "int shift_acc = GET_MODE_BITSIZE (val_mode) = %d\n", shift_acc);
	  unsigned HOST_WIDE_INT mask = GET_MODE_MASK (val_mode);
    fprintf(stderr, "unsigned HOST_WIDE_INT mask = GET_MODE_MASK (val_mode) = %u\n",  mask);
	  HOST_WIDE_INT tmp_val = val;
    fprintf(stderr, "HOST_WIDE_INT tmp_val = val = %u\n",  tmp_val);
	  for (i = 0; i < nunits; i++)
	    {
	      tmp_val = (val >> shift) & mask;
        fprintf(stderr, "Iter %d\ntmp_val = (val >> shift) & mask = %u\n",  i, tmp_val);
	      RTVEC_ELT (v, i) = gen_int_mode (tmp_val, val_mode);
	      shift += shift_acc;
        fprintf(stderr, "shift += shift_acc = %d\n",  shift);
	    }

	  arg = copy_to_mode_reg (mode, gen_rtx_CONST_VECTOR (mode, v));
	}
      else
	{
	  convert_move (tmp_rtx, arg, false);
	  arg = tmp_rtx;
	}
    }

  create_input_operand (op, arg, mode);
}

/* Take argument ARGNO from EXP's argument list and convert it into
   an expand operand.  Store the operand in *OP.  */

static void
riscv_prepare_builtin_arg (struct expand_operand *op, tree exp, unsigned argno)
{
  tree arg = CALL_EXPR_ARG (exp, argno);
  create_input_operand (op, expand_normal (arg), TYPE_MODE (TREE_TYPE (arg)));
}

/* Expand instruction ICODE as part of a built-in function sequence.
   Use the first NOPS elements of OPS as the instruction's operands.
   HAS_TARGET_P is true if operand 0 is a target; it is false if the
   instruction has no target.

   Return the target rtx if HAS_TARGET_P, otherwise return const0_rtx.  */

static rtx
riscv_expand_builtin_insn (enum insn_code icode, unsigned int n_ops,
			   struct expand_operand *ops, bool has_target_p)
{
  if (!maybe_expand_insn (icode, n_ops, ops))
    {
      error ("invalid argument to built-in function");
      return has_target_p ? gen_reg_rtx (ops[0].mode) : const0_rtx;
    }

  return has_target_p ? ops[0].value : const0_rtx;
}

/* Expand a RISCV_BUILTIN_DIRECT or RISCV_BUILTIN_DIRECT_NO_TARGET function;
   HAS_TARGET_P says which.  EXP is the CALL_EXPR that calls the function
   and ICODE is the code of the associated .md pattern.  TARGET, if nonnull,
   suggests a good place to put the result.  */

static rtx
riscv_expand_builtin_direct (enum insn_code icode, rtx target, tree exp,
			     bool has_target_p)
{
  struct expand_operand ops[MAX_RECOG_OPERANDS];

  /* Map any target to operand 0.  */
  int opno = 0;
  if (has_target_p)
    create_output_operand (&ops[opno++], target, TYPE_MODE (TREE_TYPE (exp)));

  /* Map the arguments to the other operands.  */
  gcc_assert (opno + call_expr_nargs (exp)
	      == insn_data[icode].n_generator_args);
  for (int argno = 0; argno < call_expr_nargs (exp); argno++)
    if (TARGET_RVP)
      riscv_rvp_prepare_builtin_arg (&ops[opno++], exp, argno, icode, has_target_p);
    else
      riscv_prepare_builtin_arg (&ops[opno++], exp, argno);
  return riscv_expand_builtin_insn (icode, opno, ops, has_target_p);
}

/* Implement TARGET_EXPAND_BUILTIN.  */

rtx
riscv_expand_builtin (tree exp, rtx target, rtx subtarget ATTRIBUTE_UNUSED,
		      machine_mode mode ATTRIBUTE_UNUSED,
		      int ignore ATTRIBUTE_UNUSED)
{
  tree fndecl = TREE_OPERAND (CALL_EXPR_FN (exp), 0);
  unsigned int fcode = DECL_MD_FUNCTION_CODE (fndecl);
  const struct riscv_builtin_description *d = &riscv_builtins[fcode];

  switch (d->builtin_type)
    {
    case RISCV_BUILTIN_DIRECT:
      return riscv_expand_builtin_direct (d->icode, target, exp, true);

    case RISCV_BUILTIN_DIRECT_NO_TARGET:
      return riscv_expand_builtin_direct (d->icode, target, exp, false);
    }

  gcc_unreachable ();
}

/* Implement TARGET_ATOMIC_ASSIGN_EXPAND_FENV.  */

void
riscv_atomic_assign_expand_fenv (tree *hold, tree *clear, tree *update)
{
  if (!TARGET_HARD_FLOAT)
    return;

  tree frflags = GET_BUILTIN_DECL (CODE_FOR_riscv_frflags);
  tree fsflags = GET_BUILTIN_DECL (CODE_FOR_riscv_fsflags);
  tree old_flags = create_tmp_var_raw (RISCV_ATYPE_USI);

  *hold = build4 (TARGET_EXPR, RISCV_ATYPE_USI, old_flags,
		  build_call_expr (frflags, 0), NULL_TREE, NULL_TREE);
  *clear = build_call_expr (fsflags, 1, old_flags);
  *update = NULL_TREE;
}