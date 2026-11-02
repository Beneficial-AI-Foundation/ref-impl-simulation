import Aeneas
import Real.Funs
open Aeneas Aeneas.Std Result ControlFlow Error

/-! The tail of HACL `chacha20_core` after the rounds call, cut out by a script so that it
can be reasoned about in its own declaration. `core_split` checks the cut by `rfl`. -/

namespace Real

def coreTail (k3 : Slice Std.U32) (ctx : Slice Std.U32) (ctr : Std.U32) :
  Result (Slice Std.U32)
  := do
  let i2 ← hacl.chacha20.chacha20_core.i
  let i3 ← lift (UScalar.cast .Usize i2)
  let i4 ← Slice.index_usize k3 i3
  let i5 ← lift (UScalar.cast .Usize i2)
  let i6 ← Slice.index_usize ctx i5
  let x ← lift (core.num.U32.wrapping_add i4 i6)
  let ((s3, s4), split_at_mut_back) ←
    core.slice.Slice.split_at_mut k3 0#usize
  let i7 ← lift (UScalar.cast .Usize i2)
  let s5 ← Slice.update s4 i7 x
  let i8 ← hacl.chacha20.chacha20_core.i_1
  let i9 ← lift (UScalar.cast .Usize i8)
  let k4 := split_at_mut_back (s3, s5)
  let i10 ← Slice.index_usize k4 i9
  let i11 ← lift (UScalar.cast .Usize i8)
  let i12 ← Slice.index_usize ctx i11
  let x1 ← lift (core.num.U32.wrapping_add i10 i12)
  let ((s6, s7), split_at_mut_back1) ←
    core.slice.Slice.split_at_mut k4 0#usize
  let i13 ← lift (UScalar.cast .Usize i8)
  let s8 ← Slice.update s7 i13 x1
  let i14 ← hacl.chacha20.chacha20_core.i_2
  let i15 ← lift (UScalar.cast .Usize i14)
  let k5 := split_at_mut_back1 (s6, s8)
  let i16 ← Slice.index_usize k5 i15
  let i17 ← lift (UScalar.cast .Usize i14)
  let i18 ← Slice.index_usize ctx i17
  let x2 ← lift (core.num.U32.wrapping_add i16 i18)
  let ((s9, s10), split_at_mut_back2) ←
    core.slice.Slice.split_at_mut k5 0#usize
  let i19 ← lift (UScalar.cast .Usize i14)
  let s11 ← Slice.update s10 i19 x2
  let i20 ← hacl.chacha20.chacha20_core.i_3
  let i21 ← lift (UScalar.cast .Usize i20)
  let k6 := split_at_mut_back2 (s9, s11)
  let i22 ← Slice.index_usize k6 i21
  let i23 ← lift (UScalar.cast .Usize i20)
  let i24 ← Slice.index_usize ctx i23
  let x3 ← lift (core.num.U32.wrapping_add i22 i24)
  let ((s12, s13), split_at_mut_back3) ←
    core.slice.Slice.split_at_mut k6 0#usize
  let i25 ← lift (UScalar.cast .Usize i20)
  let s14 ← Slice.update s13 i25 x3
  let i26 ← hacl.chacha20.chacha20_core.i_4
  let i27 ← lift (UScalar.cast .Usize i26)
  let k7 := split_at_mut_back3 (s12, s14)
  let i28 ← Slice.index_usize k7 i27
  let i29 ← lift (UScalar.cast .Usize i26)
  let i30 ← Slice.index_usize ctx i29
  let x4 ← lift (core.num.U32.wrapping_add i28 i30)
  let ((s15, s16), split_at_mut_back4) ←
    core.slice.Slice.split_at_mut k7 0#usize
  let i31 ← lift (UScalar.cast .Usize i26)
  let s17 ← Slice.update s16 i31 x4
  let i32 ← hacl.chacha20.chacha20_core.i_5
  let i33 ← lift (UScalar.cast .Usize i32)
  let k8 := split_at_mut_back4 (s15, s17)
  let i34 ← Slice.index_usize k8 i33
  let i35 ← lift (UScalar.cast .Usize i32)
  let i36 ← Slice.index_usize ctx i35
  let x5 ← lift (core.num.U32.wrapping_add i34 i36)
  let ((s18, s19), split_at_mut_back5) ←
    core.slice.Slice.split_at_mut k8 0#usize
  let i37 ← lift (UScalar.cast .Usize i32)
  let s20 ← Slice.update s19 i37 x5
  let i38 ← hacl.chacha20.chacha20_core.i_6
  let i39 ← lift (UScalar.cast .Usize i38)
  let k9 := split_at_mut_back5 (s18, s20)
  let i40 ← Slice.index_usize k9 i39
  let i41 ← lift (UScalar.cast .Usize i38)
  let i42 ← Slice.index_usize ctx i41
  let x6 ← lift (core.num.U32.wrapping_add i40 i42)
  let ((s21, s22), split_at_mut_back6) ←
    core.slice.Slice.split_at_mut k9 0#usize
  let i43 ← lift (UScalar.cast .Usize i38)
  let s23 ← Slice.update s22 i43 x6
  let i44 ← hacl.chacha20.chacha20_core.i_7
  let i45 ← lift (UScalar.cast .Usize i44)
  let k10 := split_at_mut_back6 (s21, s23)
  let i46 ← Slice.index_usize k10 i45
  let i47 ← lift (UScalar.cast .Usize i44)
  let i48 ← Slice.index_usize ctx i47
  let x7 ← lift (core.num.U32.wrapping_add i46 i48)
  let ((s24, s25), split_at_mut_back7) ←
    core.slice.Slice.split_at_mut k10 0#usize
  let i49 ← lift (UScalar.cast .Usize i44)
  let s26 ← Slice.update s25 i49 x7
  let i50 ← hacl.chacha20.chacha20_core.i_8
  let i51 ← lift (UScalar.cast .Usize i50)
  let k11 := split_at_mut_back7 (s24, s26)
  let i52 ← Slice.index_usize k11 i51
  let i53 ← lift (UScalar.cast .Usize i50)
  let i54 ← Slice.index_usize ctx i53
  let x8 ← lift (core.num.U32.wrapping_add i52 i54)
  let ((s27, s28), split_at_mut_back8) ←
    core.slice.Slice.split_at_mut k11 0#usize
  let i55 ← lift (UScalar.cast .Usize i50)
  let s29 ← Slice.update s28 i55 x8
  let i56 ← hacl.chacha20.chacha20_core.i_9
  let i57 ← lift (UScalar.cast .Usize i56)
  let k12 := split_at_mut_back8 (s27, s29)
  let i58 ← Slice.index_usize k12 i57
  let i59 ← lift (UScalar.cast .Usize i56)
  let i60 ← Slice.index_usize ctx i59
  let x9 ← lift (core.num.U32.wrapping_add i58 i60)
  let ((s30, s31), split_at_mut_back9) ←
    core.slice.Slice.split_at_mut k12 0#usize
  let i61 ← lift (UScalar.cast .Usize i56)
  let s32 ← Slice.update s31 i61 x9
  let i62 ← hacl.chacha20.chacha20_core.i_10
  let i63 ← lift (UScalar.cast .Usize i62)
  let k13 := split_at_mut_back9 (s30, s32)
  let i64 ← Slice.index_usize k13 i63
  let i65 ← lift (UScalar.cast .Usize i62)
  let i66 ← Slice.index_usize ctx i65
  let x10 ← lift (core.num.U32.wrapping_add i64 i66)
  let ((s33, s34), split_at_mut_back10) ←
    core.slice.Slice.split_at_mut k13 0#usize
  let i67 ← lift (UScalar.cast .Usize i62)
  let s35 ← Slice.update s34 i67 x10
  let i68 ← hacl.chacha20.chacha20_core.i_11
  let i69 ← lift (UScalar.cast .Usize i68)
  let k14 := split_at_mut_back10 (s33, s35)
  let i70 ← Slice.index_usize k14 i69
  let i71 ← lift (UScalar.cast .Usize i68)
  let i72 ← Slice.index_usize ctx i71
  let x11 ← lift (core.num.U32.wrapping_add i70 i72)
  let ((s36, s37), split_at_mut_back11) ←
    core.slice.Slice.split_at_mut k14 0#usize
  let i73 ← lift (UScalar.cast .Usize i68)
  let s38 ← Slice.update s37 i73 x11
  let i74 ← hacl.chacha20.chacha20_core.i_12
  let i75 ← lift (UScalar.cast .Usize i74)
  let k15 := split_at_mut_back11 (s36, s38)
  let i76 ← Slice.index_usize k15 i75
  let i77 ← lift (UScalar.cast .Usize i74)
  let i78 ← Slice.index_usize ctx i77
  let x12 ← lift (core.num.U32.wrapping_add i76 i78)
  let ((s39, s40), split_at_mut_back12) ←
    core.slice.Slice.split_at_mut k15 0#usize
  let i79 ← lift (UScalar.cast .Usize i74)
  let s41 ← Slice.update s40 i79 x12
  let i80 ← hacl.chacha20.chacha20_core.i_13
  let i81 ← lift (UScalar.cast .Usize i80)
  let k16 := split_at_mut_back12 (s39, s41)
  let i82 ← Slice.index_usize k16 i81
  let i83 ← lift (UScalar.cast .Usize i80)
  let i84 ← Slice.index_usize ctx i83
  let x13 ← lift (core.num.U32.wrapping_add i82 i84)
  let ((s42, s43), split_at_mut_back13) ←
    core.slice.Slice.split_at_mut k16 0#usize
  let i85 ← lift (UScalar.cast .Usize i80)
  let s44 ← Slice.update s43 i85 x13
  let i86 ← hacl.chacha20.chacha20_core.i_14
  let i87 ← lift (UScalar.cast .Usize i86)
  let k17 := split_at_mut_back13 (s42, s44)
  let i88 ← Slice.index_usize k17 i87
  let i89 ← lift (UScalar.cast .Usize i86)
  let i90 ← Slice.index_usize ctx i89
  let x14 ← lift (core.num.U32.wrapping_add i88 i90)
  let ((s45, s46), split_at_mut_back14) ←
    core.slice.Slice.split_at_mut k17 0#usize
  let i91 ← lift (UScalar.cast .Usize i86)
  let s47 ← Slice.update s46 i91 x14
  let i92 ← hacl.chacha20.chacha20_core.i_15
  let i93 ← lift (UScalar.cast .Usize i92)
  let k18 := split_at_mut_back14 (s45, s47)
  let i94 ← Slice.index_usize k18 i93
  let i95 ← lift (UScalar.cast .Usize i92)
  let i96 ← Slice.index_usize ctx i95
  let x15 ← lift (core.num.U32.wrapping_add i94 i96)
  let ((s48, s49), split_at_mut_back15) ←
    core.slice.Slice.split_at_mut k18 0#usize
  let i97 ← lift (UScalar.cast .Usize i92)
  let s50 ← Slice.update s49 i97 x15
  let k19 := split_at_mut_back15 (s48, s50)
  let i98 ← Slice.index_usize k19 12#usize
  let i99 ← lift (core.num.U32.wrapping_add i98 ctr)
  Slice.update k19 12#usize i99


theorem core_split (k ctx : Slice Std.U32) (ctr : Std.U32) :
    hacl.chacha20.chacha20_core k ctx ctr = (do
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U32) k
          { start := 0#usize, «end» := 16#usize }
      let s1 ←
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
          Std.U32) ctx { start := 0#usize, «end» := 16#usize }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU32 s s1
      let k1 := index_mut_back s2
      let i ← Slice.index_usize k1 12#usize
      let i1 ← lift (core.num.U32.wrapping_add i ctr)
      let k2 ← Slice.update k1 12#usize i1
      let k3 ← hacl.chacha20.rounds k2
      coreTail k3 ctx ctr) := by
  rfl

end Real
