module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Call
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.ByteWords

/-! # A call of `vg_rsa_mont_mul` at offsets of the working space

For any width `n` and offsets `m`, `inv`, `s`, `o`, `a` and `b` of the
working space that meet the callee's precondition (`Offs`): a block that
stores them as the nine arguments into a frame of 36 bytes below `esp`
(`callArg`), then a call of `vg_rsa_mont_mul`, writes the Montgomery
product of the numbers at `a` and `b` at `o`, changing only it, the callee's
range and the 96 bytes of stack below `esp` (`call_ok`). The functions at a
run-time width state their multiplications from it.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.RtCall

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (calleeOf setWidth_toNat callee_frame rtPre_of ofs_in ofs_out ofs_eq
  rtBody_noSp rtBody_stackUse callee_pre)
open VG.Proof.Rsa.MontMul (Apart scratchBytes)

/-- The words of a call's frame: `ws`, `ws_len`, the width and the offsets. -/
def callArg (edi wsLen : BitVec 32) (n m inv sc o a b : Nat) : Nat → BitVec 32
  | 0 => edi
  | 1 => wsLen
  | 2 => BitVec.ofNat 32 n
  | 3 => BitVec.ofNat 32 m
  | 4 => BitVec.ofNat 32 inv
  | 5 => BitVec.ofNat 32 sc
  | 6 => BitVec.ofNat 32 o
  | 7 => BitVec.ofNat 32 a
  | _ => BitVec.ofNat 32 b

/-- The offsets of a call: within the working space, and apart as the callee needs. -/
structure Offs (bytes n m inv sc o a b : Nat) : Prop where
  pos : 0 < n
  m_le : m + 8 * n ≤ bytes
  inv_le : inv + 4 ≤ bytes
  s_le : sc + scratchBytes n ≤ bytes
  o_le : o + 8 * n ≤ bytes
  a_le : a + 8 * n ≤ bytes
  b_le : b + 8 * n ≤ bytes
  smo : Apart m (8 * n) (sc, scratchBytes n)
  sinv : Apart inv 4 (sc, scratchBytes n)
  so : Apart o (8 * n) (sc, scratchBytes n)
  sa : Apart a (8 * n) (sc, scratchBytes n)
  sb : Apart b (8 * n) (sc, scratchBytes n)
  omo : Apart o (8 * n) (m, 8 * n)
  oinv : Apart o (8 * n) (inv, 4)

section
variable {s g : State} {base : Addr} {bytes n m inv sc o a b : Nat} {wsLen : BitVec 32}

theorem callee_arg (low : 96 ≤ (s.gpr .esp).toNat) (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36)
    (hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (s.gpr .edi) wsLen n m inv sc o a b i) {i : Nat} (hi : i < 9) :
    arg (calleeOf g base bytes) i = callArg (s.gpr .edi) wsLen n m inv sc o a b i := by
  have hsp := (s.gpr .esp).isLt
  have gEsp : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [hesp, VG.X86.sub_toNat (by omega)]
  show arg g.callEntry i = _
  rw [arg_callEntry (by omega) (by omega)]
  have e := addr_eq (x := g.gpr .esp) (k := 4 * i) (by omega)
  simp only [addr] at e
  rw [e, hread i hi]

theorem callee_abi (scr : Scr s base bytes) (hbytes : bytes = wsLen.toNat * 8)
    (R : CallRoom (s.gpr .esp) base bytes) (O : Offs bytes n m inv sc o a b)
    (hesp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36)
    (hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem)
    (hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (s.gpr .edi) wsLen n m inv sc o a b i)
    (hinv : (val32 s.mem base m (2 * n) * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b (2 * n) < val32 s.mem base m (2 * n)) :
    RtABI (calleeOf g base bytes) := by
  have low := R.low
  have low40 : 40 ≤ (s.gpr .esp).toNat := by omega
  have hsp := (s.gpr .esp).isLt
  have nwr := scr.nowrap
  have blt := scr.size_lt
  have gEsp : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [hesp, VG.X86.sub_toNat (by omega)]
  have argc := fun i (hi : i < 9) => callee_arg (base := base) (bytes := bytes) low hesp hread hi
  have vn : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 32 v).toNat = v := fun hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have O1 := O.pos
  have O2 := O.m_le
  have O3 := O.inv_le
  have O4 := O.s_le
  have O5 := O.o_le
  have O6 := O.a_le
  have O7 := O.b_le
  have v0 : (arg (calleeOf g base bytes) 0).toNat = base.toNat := by rw [argc 0 (by decide)]; exact scr.edi_toNat
  have v1 : (arg (calleeOf g base bytes) 1).toNat * 8 = bytes := by rw [argc 1 (by decide)]; exact hbytes.symm
  have v2 : (arg (calleeOf g base bytes) 2).toNat = n := by
    rw [argc 2 (by decide)]; exact vn (by omega)
  have v3 : (arg (calleeOf g base bytes) 3).toNat = m := by rw [argc 3 (by decide)]; exact vn (by omega)
  have v4 : (arg (calleeOf g base bytes) 4).toNat = inv := by rw [argc 4 (by decide)]; exact vn (by omega)
  have v5 : (arg (calleeOf g base bytes) 5).toNat = sc := by
    rw [argc 5 (by decide)]; exact vn (by simp only [scratchBytes] at O4; omega)
  have v6 : (arg (calleeOf g base bytes) 6).toNat = o := by rw [argc 6 (by decide)]; exact vn (by omega)
  have v7 : (arg (calleeOf g base bytes) 7).toNat = a := by rw [argc 7 (by decide)]; exact vn (by omega)
  have v8 : (arg (calleeOf g base bytes) 8).toNat = b := by rw [argc 8 (by decide)]; exact vn (by omega)
  have ws : wsOf (calleeOf g base bytes) = base := by
    show (arg (calleeOf g base bytes) 0).setWidth 64 = base
    rw [argc 0 (by decide)]; exact scr.edi
  have ln : lenOf (calleeOf g base bytes) = bytes := v1
  have v1' : 8 * (arg (calleeOf g base bytes) 1).toNat = bytes := by omega
  have Fc := callee_frame (base := base) (bytes := bytes) low hesp hFg
  have numc : ∀ d k, d + k ≤ bytes → Proof.Rsa.MontMul.numAt (calleeOf g base bytes).mem base d k =
      Proof.Rsa.MontMul.numAt s.mem base d k := fun d k hdk => by
    unfold Proof.Rsa.MontMul.numAt
    rw [Fc.read (r := ⟨base, bytes⟩) (Offset.contains_base _ hdk (by omega))
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact R.apart40.symm) (by omega)]
  have argAddr0 : argAddr (calleeOf g base bytes) 0 = (g.gpr .esp).setWidth 64 := by
    show argAddr g.callEntry 0 = _
    rw [argAddr_callEntry]; simp
  have retBase : ((calleeOf g base bytes).gpr .esp).setWidth 64 = (g.gpr .esp - 4).setWidth 64 := by
    simp [calleeOf]
  have e8 : 8 * n = 4 * (2 * n) := by omega
  refine ⟨?_, rfl, by rw [ws, ln]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · show (g.gpr .esp - 4).toNat + 4 + 36 ≤ 2 ^ 32
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]; omega
  · rw [ws, ln, argAddr0, hesp]; exact (R.apart.sub_left (below_sub (by decide) low)).symm
  · rw [retBase, ws, ln, hesp]; exact R.apart.sub_left (below_inner (a := 4) (k := 36) (b := 96) (by decide) low)
  · rw [retBase, argAddr0]
    refine Region.disjoint_of_le (.inl ?_) ?_ ?_ <;> simp only [setWidth_toNat] <;>
      (try rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]) <;> omega
  · rw [v0, ln]; exact nwr
  · rw [v2]; exact O1
  · rw [v3, v2, v1']; exact O2
  · rw [v4, v1']; exact O3
  · rw [v5, v2, v1']; exact O4
  · rw [v6, v2, v1']; exact O5
  · rw [v7, v2, v1']; exact O6
  · rw [v8, v2, v1']; exact O7
  · rw [v3, v5, v2]; exact O.smo
  · rw [v4, v5, v2]; exact O.sinv
  · rw [v6, v5, v2]; exact O.so
  · rw [v7, v5, v2]; exact O.sa
  · rw [v8, v5, v2]; exact O.sb
  · rw [v6, v3, v2]; exact O.omo
  · rw [v6, v4, v2]; exact O.oinv
  · rw [ws, v3, v2, v4, numc _ _ O2, numc _ _ O3, numAt_val32, numAt_w32]
    exact hinv
  · rw [ws, v8, v3, v2, numc _ _ O7, numc _ _ O2, numAt_val32, numAt_val32]
    exact hB

end

/-- The block storing the arguments, and the call. -/
abbrev callCode (is : List Instr) : Prog isa :=
  .frame (.alloc 36) (.seq (.block is) (.call "vg_rsa_mont_mul_at" Sse2.atBody)) (.free 36)

theorem call_ok {s : State} {base : Addr} {bytes n m inv sc o a b : Nat} {wsLen : BitVec 32} {is : List Instr}
    (scr : Scr s base bytes) (hbytes : bytes = wsLen.toNat * 8) (R : CallRoom (s.gpr .esp) base bytes)
    (O : Offs bytes n m inv sc o a b)
    (hinv : (val32 s.mem base m (2 * n) * w32 s.mem base inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base b (2 * n) < val32 s.mem base m (2 * n))
    (hns : NoSp (.seq (.block is) (.call "vg_rsa_mont_mul_at" Sse2.atBody) : Prog isa))
    (hargs : WP isa (.block is) (allocFrame 36 s) fun g =>
      Keeps [.eax, .edx] (allocFrame 36 s) g ∧
      Frame [⟨((allocFrame 36 s).gpr .esp).setWidth 64, 36⟩] (allocFrame 36 s).mem g.mem ∧
      ∀ i < 9, g.mem.readW (((allocFrame 36 s).gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (s.gpr .edi) wsLen n m inv sc o a b i) :
    WP isa (callCode is) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base o, 8 * n⟩, ⟨off base sc, scratchBytes n⟩, below (s.gpr .esp) 96] s.mem t.mem ∧
      val32 t.mem base o (2 * n) < val32 s.mem base m (2 * n) ∧
      val32 t.mem base o (2 * n) * 2 ^ (64 * n) % val32 s.mem base m (2 * n) =
        val32 s.mem base a (2 * n) * val32 s.mem base b (2 * n) % val32 s.mem base m (2 * n) := by
  have low := R.low
  have low40 : 40 ≤ (s.gpr .esp).toNat := by omega
  have hsp := (s.gpr .esp).isLt
  have nwr := scr.nowrap
  unfold callCode
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) hns ?_
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  refine WP.seq (WP.mono hargs fun g ⟨Kg, Fg, Rg⟩ => ?_)
  have gEsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by rw [Kg.1 _ (by decide), fEsp]
  have hFg : Frame [below (s.gpr .esp) 36] s.mem g.mem := by
    have := Fg; rwa [fEsp, allocFrame_mem] at this
  have hread : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) wsLen n m inv sc o a b i := by
    intro i hi; rw [Kg.1 _ (by decide), Rg i hi]
  have A := callee_abi scr hbytes R O gEsp hFg hread hinv hB
  have Fc := callee_frame (base := base) (bytes := bytes) low gEsp hFg
  have gEspN : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by rw [gEsp, VG.X86.sub_toNat (by omega)]
  have hframe : (⟨(g.gpr .esp).setWidth 64, 36⟩ : Region) ∈ g.wr := by
    rw [Kg.2.2, allocFrame_wr, gEsp]; exact List.mem_cons_self ..
  have hscr : (⟨base, bytes⟩ : Region) ∈ g.wr := by
    rw [Kg.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ scr.wr
  have argA : argAddr g.callEntry 0 = (g.gpr .esp).setWidth 64 := by rw [argAddr_callEntry]; simp
  have low96 := R.low
  refine WP.call (k := Proof.Rsa.MontMul.mulContract abi 56) (rd := [⟨argAddr g.callEntry 0, 36⟩])
    (wr := [⟨base, bytes⟩]) VG.Proof.Mont.X86.Sse2.at_correct rtBody_noSp (by rw [rtBody_stackUse]; omega)
    (callee_pre A R gEsp)
    (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_) fun s' rd' wr' cs' F _ ⟨s₂, m₂, _, post⟩ => ?_
  · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
    · rw [argA]; exact List.mem_append_right _ hframe
    · exact List.mem_append_right _ hscr
  · rw [List.mem_singleton.mp hr]; exact hscr
  change (Proof.Rsa.MontMul.mulContract abi 56).post (calleeOf g base bytes) s₂ at post
  sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes] at post
  obtain ⟨L₂, C₂, K₂⟩ := post
  have blt := scr.size_lt
  have ca := fun i (hi : i < 9) => callee_arg (base := base) (bytes := bytes) low gEsp hread hi
  have vn : ∀ {v : Nat}, v < 2 ^ 32 → (BitVec.ofNat 32 v).toNat = v := fun hv => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have O1 := O.pos
  have O2 := O.m_le
  have O4 := O.s_le
  have O5 := O.o_le
  have O6 := O.a_le
  have O7 := O.b_le
  have w0 : BitVec.setWidth 64 (arg (calleeOf g base bytes) 0) = base := by
    rw [ca 0 (by decide)]; exact scr.edi
  have w1 : (arg (calleeOf g base bytes) 1).toNat = wsLen.toNat := by rw [ca 1 (by decide)]; rfl
  have w2 : (arg (calleeOf g base bytes) 2).toNat = n := by rw [ca 2 (by decide)]; exact vn (by omega)
  have w3 : (arg (calleeOf g base bytes) 3).toNat = m := by rw [ca 3 (by decide)]; exact vn (by omega)
  have w5 : (arg (calleeOf g base bytes) 5).toNat = sc := by
    rw [ca 5 (by decide)]; exact vn (by simp only [scratchBytes] at O4; omega)
  have w6 : (arg (calleeOf g base bytes) 6).toNat = o := by rw [ca 6 (by decide)]; exact vn (by omega)
  have w7 : (arg (calleeOf g base bytes) 7).toNat = a := by rw [ca 7 (by decide)]; exact vn (by omega)
  have w8 : (arg (calleeOf g base bytes) 8).toNat = b := by rw [ca 8 (by decide)]; exact vn (by omega)
  have e8 : 8 * n = 4 * (2 * n) := by omega
  simp only [w0, w1, w2, w3, w5, w6, w7, w8, numAt_val32] at L₂ C₂ K₂
  have Fc' : Frame [below (s.gpr .esp) 40] s.mem (g.mem.writeW ((g.gpr .esp - 4).setWidth 64) (g.unknowns 0)) := Fc
  have vc : ∀ d, d + 8 * n ≤ bytes →
      val32 (g.mem.writeW ((g.gpr .esp - 4).setWidth 64) (g.unknowns 0)) base d (2 * n) =
        val32 s.mem base d (2 * n) := fun d hd => by
    rw [← read_eq_val32, ← read_eq_val32, Fc'.read (r := ⟨base, bytes⟩)
      (Offset.contains_base _ (by rw [← e8]; exact hd) (by omega))
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact R.apart40.symm) (by omega)]
  rw [vc _ O2] at L₂ C₂
  rw [vc _ O6, vc _ O7] at C₂
  refine ⟨fun r hr => ?_, by rw [freed_rd, rd', Kg.2.1, allocFrame_rd],
    by rw [freed_wr, wr', Kg.2.2, allocFrame_wr]; rfl, fun x hx => ?_,
    by rw [freed_mem, ← m₂]; exact L₂, by rw [freed_mem, ← m₂]; exact C₂⟩
  · by_cases he : r = .esp
    · subst he
      rw [freed_esp, cs' _ hr, gEsp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ he, cs' _ hr, Kg.1 _ (by revert hr; cases r <;> simp [calleeSaved]),
        allocFrame_gpr _ _ he]
  · have nst96 : ¬ (below (s.gpr .esp) 96).Contains x 1 := hx _ (by simp)
    have nst : ¬ (below (s.gpr .esp) 40).Contains x 1 := fun hc => nst96 (below_sub (by decide) low96 x hc)
    have nos : ¬ (⟨off base sc, scratchBytes n⟩ : Region).Contains x 1 := hx _ (by simp)
    have noo : ¬ (⟨off base o, 8 * n⟩ : Region).Contains x 1 := hx _ (by simp)
    rw [freed_mem]
    by_cases hin : (⟨base, bytes⟩ : Region).Contains x 1
    · have hi := ofs_in hin
      have os := ofs_out nos
      have oo := ofs_out noo
      rw [← m₂, ofs_eq base x, K₂ _ (by rw [hbytes] at hi; omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact os
        · exact oo), ← ofs_eq base x]
      exact Fc' x fun r hr => by rw [List.mem_singleton.mp hr]; exact nst
    · rw [F x fun r hr => ?_]
      · exact hFg x fun r hr => by
          rw [List.mem_singleton.mp hr]; exact fun hc => nst (below_sub (by decide) low40 x hc)
      · rcases List.mem_append.mp hr with hr | hr <;> rw [List.mem_singleton.mp hr]
        · exact hin
        · rw [rtBody_stackUse, gEsp]
          exact fun hc => nst96 (below_inner (a := 56 + 4) (k := 36) (b := 96) (by decide) low96 x hc)

end VG.Proof.Bignum.X86.RtCall
