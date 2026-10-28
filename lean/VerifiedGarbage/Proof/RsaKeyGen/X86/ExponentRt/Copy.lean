module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.MillerRabin.X86.SelectLoop
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Saving the candidate minus one into array 5, and restoring it, at a run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

/-- `copyCount`: `esi = 2 w` words, and the mask `ecx` of a copy. -/
theorem copyCount_ok {s : State} {base : Addr} {size w : Nat} {is : List Instr} {Q : State → Prop}
    (S : Scr s base size) (header : 8 ≤ size) (hw : w ≤ 64)
    (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (k : ∀ u, Keeps [.esi, .ecx] s u → u.mem = s.mem → (u.gpr .esi).toNat = 2 * w →
      u.gpr .ecx = BitVec.allOnes 32 → WP isa (.block is) u Q) :
    WP isa (.block (copyCount ++ is)) s Q := by
  simp only [copyCount, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc S (by omega)) fun a A _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun b B => wp_movS rfl fun u U _ => ?_
  have K : Keeps [.esi, .ecx] s u := ((A.keeps.trans B.keeps).mono (by decide)).trans (U.keeps.mono (by decide))
  refine k u K (by rw [U.mem, B.mem, A.mem]) ?_ U.gpr
  rw [U.other .esi (by decide), B.gpr, A.gpr, len, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  omega

/-- `copyLoop` over `N` words from `y` to `x`. -/
theorem copyLoop_ok {s : State} {W : Addr} {L x y N : Nat} (hw : Ws s W L)
    (positive : 0 < N) (dstFit : x + 4 * N ≤ L) (srcFit : y + 4 * N ≤ L)
    (apart : x + 4 * N ≤ y ∨ y + 4 * N ≤ x)
    (dst : PtrAt s W .ebx x) (src : PtrAt s W .ebp y) (count : (s.gpr .esi).toNat = N)
    (mask : s.gpr .ecx = BitVec.allOnes 32) :
    WP isa copyLoop s fun t =>
      Outside W x (4 * N) s.mem t.mem ∧ val32 t.mem W x N = val32 s.mem W y N ∧
      Keeps [.eax, .ebx, .ebp, .esi] s t :=
  VG.Proof.MillerRabin.X86.selectLoop_ok hw positive dstFit srcFit apart dst src count true
    (by rw [mask]; rfl)

theorem saveSetup_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (hw : w ≤ 64)
    (header : 8 ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block saveSetup) s
      fun d => Keeps [.ebx, .edx, .esi, .ecx, .ebp] s d ∧ d.mem = s.mem ∧
        d.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 256 ∧ d.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
        (d.gpr .esi).toNat = 2 * w ∧ d.gpr .ecx = BitVec.allOnes 32 := by
  simp only [saveSetup, List.cons_append]
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have Kb : Keeps [.ebp] s b := (A.keeps.trans B.keeps)
  have Sb := S.of_keeps Kb (by decide)
  have edib : b.gpr .edi = s.gpr .edi := Kb.1 .edi (by decide)
  refine savedPtr_ok Sb header (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebx => ?_
  have Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc header hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  refine ⟨(Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kd.mono (by decide))),
    by rw [Md, Mc, B.mem, A.mem], ?_, ?_, esi, ecx⟩
  · rw [Kd.1 .ebp (by decide), Kc.1 .ebp (by decide), B.gpr, A.gpr]; rfl
  · rw [Kd.1 .ebx (by decide), ebx, edib]

theorem restoreSetup_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (hw : w ≤ 64)
    (header : 8 ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w)) :
    WP isa (.block restoreSetup) s
      fun d => Keeps [.ebx, .edx, .esi, .ecx, .ebp] s d ∧ d.mem = s.mem ∧
        d.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 256 ∧ d.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
        (d.gpr .esi).toNat = 2 * w ∧ d.gpr .ecx = BitVec.allOnes 32 := by
  simp only [restoreSetup, List.cons_append]
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have Kb : Keeps [.ebx] s b := (A.keeps.trans B.keeps)
  have Sb := S.of_keeps Kb (by decide)
  have edib : b.gpr .edi = s.gpr .edi := Kb.1 .edi (by decide)
  refine savedPtr_ok Sb header (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebp => ?_
  have Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc header hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  refine ⟨(Kb.mono (by decide)).trans ((Kc.mono (by decide)).trans (Kd.mono (by decide))),
    by rw [Md, Mc, B.mem, A.mem], ?_, ?_, esi, ecx⟩
  · rw [Kd.1 .ebx (by decide), Kc.1 .ebx (by decide), B.gpr, A.gpr]; rfl
  · rw [Kd.1 .ebp (by decide), ebp, edib]

theorem save_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (odd : val32 s.mem base (slot w 0) (2 * w) % 2 = 1) :
    WP isa save s fun t =>
      val32 t.mem base (slot w 5) (2 * w) + 1 = val32 s.mem base (slot w 0) (2 * w) ∧
      Outside base (slot w 5) (8 * w) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lo := slot5_ge w
  have nowrap := S.nowrap
  rw [slot0_eq] at odd ⊢
  have hws : Ws s base size := ⟨S.wr, S.nowrap⟩
  unfold save saveSetup
  simp only [List.cons_append]
  refine WP.seq (wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_)
  have Kb : Keeps [.ebp] s b := (A.keeps.trans B.keeps)
  have Sb := S.of_keeps Kb (by decide)
  have ebp : b.gpr .ebp = b.gpr .edi + BitVec.ofNat 32 256 := by
    rw [B.gpr, A.gpr, Kb.1 .edi (by decide)]; rfl
  refine savedPtr_ok Sb (by omega) (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebx => ?_
  have Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc (by omega) hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  have Kbd : Keeps [.ebx, .edx, .esi, .ecx] b d := (Kc.mono (by decide)).trans (Kd.mono (by decide))
  have Sd := Sb.of_keeps Kbd (by decide)
  have edi : d.gpr .edi = b.gpr .edi := Kbd.1 .edi (by decide)
  have Md' : d.mem = s.mem := by rw [Md, Mc, B.mem, A.mem]
  have K6 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.mono (by decide)).trans (Kbd.mono (by decide))
  refine WP.seq (WP.mono (copyLoop_ok (hws.of_keeps K6) (x := slot w 5) (y := 256) (N := 2 * w) (by omega) (by omega) (by omega)
    (by omega) (ptrAt_edi Sd (by rw [Kd.1 .ebx (by decide), ebx, edi]))
    (ptrAt_edi Sd (by rw [Kbd.1 .ebp (by decide), ebp, edi])) esi ecx) fun e ⟨Oe, Ve, Ke⟩ => ?_)
  have Se := Sd.of_keeps Ke (by decide)
  have Le : e.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w) :=
    (BitVec.eq_of_toNat_eq (Oe.w32 (d := 4) (Or.inl (by omega)) (by omega))).trans (by rw [Md']; exact len)
  refine WP.seq (WP.mono (savedPtr_block_ok Se (by omega) Le (by decide) (by decide) (by decide))
    fun f ⟨Kf, Mf, ebxf⟩ => ?_)
  unfold decrementAt
  have Sf := Se.of_keeps Kf (by decide)
  have Pf : PtrAt f base .ebx (slot w 5) := ptrAt_edi Sf (by rw [ebxf, Kf.1 .edi (by decide)])
  have hwf : Ws f base size := hws.of_keeps ((K6.trans (Ke.mono (by decide))).trans (Kf.mono (by decide)))
  refine wp_movS (readSrc_ptr hwf Pf (d := 0) (by omega)) fun g G _ => wp_subS rfl fun h H _ => ?_
  have Kh : Keeps [.eax] f h := G.keeps.trans H.keeps
  have Ph : PtrAt h base .ebx (slot w 5) := by rw [PtrAt, Kh.1 .ebx (by decide)]; exact Pf
  refine wp_storeS (ea_ptr (hwf.of_keeps Kh) Ph (d := 0) (by omega))
    (ws_write (hwf.of_keeps Kh) (y := slot w 5 + 0) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have copied : val32 f.mem base (slot w 5) (2 * w) = val32 s.mem base 256 (2 * w) := by
    rw [Mf, Ve, Md']
  have lowPos : 0 < w32 f.mem base (slot w 5) := by
    have := VG.Proof.RsaKeyGen.X86.LowWord.odd_low (m := f.mem) (base := base) (out := slot w 5) (n := 2 * w)
      (by omega) (by rw [copied]; exact odd)
    exact this
  have Ot : Outside base (slot w 5) 4 f.mem t.mem := by
    rw [T.mem, H.mem, G.mem, Nat.add_zero]
    exact writeW32_outside _ _ _ (by omega)
  have low : w32 t.mem base (slot w 5) + 1 = w32 f.mem base (slot w 5) := by
    simp only [T.mem, Nat.add_zero, w32_write_self, H.gpr, G.gpr]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact lowPos)]
    change w32 f.mem base (slot w 5) - 1 + 1 = _
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← copied, show 2 * w = (2 * w - 1) + 1 by omega, val32, val32,
      Ot.val32 (Or.inr (by omega)) (by omega)]
    omega
  · rw [show f.mem = e.mem from Mf] at Ot
    rw [← Md', show 8 * w = 4 * (2 * w) by omega]
    exact Oe.trans (Ot.mono (by omega) (by omega))
  · exact ((K6.trans (Ke.mono (by decide))).trans (Kf.mono (by decide))).trans
      ((Kh.mono (by decide)).widen (T.keeps []))

theorem restore_ok {s : State} {base : Addr} {size w : Nat} (S : Scr s base size) (width : 4 ≤ w) (hw : w ≤ 64)
    (space : slot w 5 + 8 * w ≤ size) (len : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 (8 * w))
    (even : val32 s.mem base (slot w 5) (2 * w) % 2 = 0) :
    WP isa restore s fun t =>
      val32 t.mem base (slot w 0) (2 * w) = val32 s.mem base (slot w 5) (2 * w) + 1 ∧
      Outside base (slot w 0) (8 * w) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have lo := slot5_ge w
  have nowrap := S.nowrap
  rw [slot0_eq]
  have hws : Ws s base size := ⟨S.wr, S.nowrap⟩
  unfold restore restoreSetup
  simp only [List.cons_append]
  refine WP.seq (wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_)
  have Kb : Keeps [.ebx] s b := (A.keeps.trans B.keeps)
  have Sb := S.of_keeps Kb (by decide)
  have ebx : b.gpr .ebx = b.gpr .edi + BitVec.ofNat 32 256 := by
    rw [B.gpr, A.gpr, Kb.1 .edi (by decide)]; rfl
  refine savedPtr_ok Sb (by omega) (by rw [B.mem, A.mem]; exact len) (by decide) (by decide) (by decide)
    fun c Kc Mc ebp => ?_
  have Sc := Sb.of_keeps Kc (by decide)
  refine copyCount_ok Sc (by omega) hw (by rw [Mc, B.mem, A.mem]; exact len) fun d Kd Md esi ecx => WP.block_nil ?_
  have Kbd : Keeps [.ebp, .edx, .esi, .ecx] b d := (Kc.mono (by decide)).trans (Kd.mono (by decide))
  have Sd := Sb.of_keeps Kbd (by decide)
  have edi : d.gpr .edi = b.gpr .edi := Kbd.1 .edi (by decide)
  have Md' : d.mem = s.mem := by rw [Md, Mc, B.mem, A.mem]
  have K6 : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s d := (Kb.mono (by decide)).trans (Kbd.mono (by decide))
  refine WP.seq (WP.mono (copyLoop_ok (hws.of_keeps K6) (x := 256) (y := slot w 5) (N := 2 * w) (by omega) (by omega) (by omega)
    (by omega) (ptrAt_edi Sd (by rw [Kbd.1 .ebx (by decide), ebx, edi]))
    (ptrAt_edi Sd (by rw [Kd.1 .ebp (by decide), ebp, edi])) esi ecx) fun e ⟨Oe, Ve, Ke⟩ => ?_)
  have Se := Sd.of_keeps Ke (by decide)
  have copied : val32 e.mem base 256 (2 * w) = val32 s.mem base (slot w 5) (2 * w) := by rw [Ve, Md']
  have bound : w32 e.mem base 256 + 1 < 2 ^ 32 :=
    VG.Proof.RsaKeyGen.X86.LowWord.even_low (n := 2 * w) (by omega) (by rw [copied]; exact even)
  refine WP.mono (VG.Proof.RsaKeyGen.X86.LowWord.increment_ok Se (n := 2 * w) (by omega) (by omega) bound)
    fun t ⟨V, Ot, Kt⟩ => ?_
  refine ⟨by rw [V, copied], ?_, ?_⟩
  · rw [← Md', show 8 * w = 4 * (2 * w) by omega]
    exact Oe.trans (Ot.mono (by omega) (by omega))
  · exact (K6.trans (Ke.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.RsaKeyGen.X86.ExponentRt
