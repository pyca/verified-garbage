module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSDiv
public import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: numbers into the key working space

`loadS L j o n` (`loadS_vp`): array `j` := the `n` big-endian bytes that a
claim puts at byte `o` of `scratch`, its words above them zero (`Top`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Rsa.Arm.Keys (hdr ptr)
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

theorem setWidth_ofNat16 {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- The top word of a number of `w + 2` words below `2^(32 w)`. -/
theorem top_of_lt {m : Mem} {base : Addr} {d w : Nat} (h : val32 m base d (w + 2) < 2 ^ (32 * w)) :
    w32 m base (d + 4 * w) = 0 := by
  have e := val32_append m base d w 2
  have lo := val32_lt m base d w
  have p := Nat.two_pow_pos (32 * w)
  have z : val32 m base (d + 4 * w) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * w) 2) with z | z
    · exact z
    · have : 2 ^ (32 * w) * 1 ≤ 2 ^ (32 * w) * val32 m base (d + 4 * w) 2 := Nat.mul_le_mul_left _ z
      omega
  have e2 := val32_append m base (d + 4 * w) 1 1
  rw [show 1 + 1 = 2 from rfl, z] at e2
  simp only [val32, Nat.add_zero, Nat.mul_zero] at e2
  omega

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Array `j` := the bytes `bs` that a claim puts at byte `o` of `scratch`. -/
theorem loadS_vp {L j o n : Nat} {bs : List Byte} (cert : Cert7 (loadS L j o n)) (hL : L = G.pLen) (hj : j < nArrs) (hbs : (o, bs) ∈ c.cl)
    (hn : bs.length = n) (hn0 : 0 < n) (hnw : n ≤ 4 * G.w) :
    VP (St G c X) (loadS L j o n)
      (fun σ t => St G { c with A := KU c.A j (Spec.Dsa.decodeBE bs), live := j :: c.live } X σ t ∧
        Top G t.mem j) := by
  refine ks_vp cert (fun σ s h => h.1) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have l := h.lens
  have oK : o + n ≤ sK G.pLen := by have := h.clOk _ hbs; simpa [hn] using this
  have hw := h.wsWith (s.rd ++ [G.rs o n])
  have nw := hw.nowrap
  have kb := h.kbNat
  have fa := hw.arr_fit hj
  have hS : S G.w = 4 * (G.w + 2) := rfl
  have w96 : G.w ≤ 96 := by simp only [GP.w]; omega
  have inS : G.rScr ∈ s.wr := by rw [gi.wr, gi.pre.wr, gi.hG]; simp
  have hR : Covers [G.rs o n] s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, o, rfl, show o + n ≤ G.scrLen * 8 by omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  have ad : State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)) = off (State.addr G.KB) (arr G.w j) :=
    hw.addr (by omega)
  have as : State.addr (G.scr + BitVec.ofNat 32 o) = G.sa o := gi.saddr (by omega)
  have e : off (State.addr G.KB) (arr G.w j) = G.sa (sK G.pLen + arr G.w j) := by
    rw [gi.kaddr]; simp only [off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have b := h.sb _ hbs
  simp only [hn] at b
  refine h.ksWPr hR rfl (P := fun t =>
      val32 t.mem (State.addr (G.KB + BitVec.ofNat 32 (arr G.w j))) 0 (G.w + 2) = Spec.Rsa.os2ip bs ∧
      Frame [⟨State.addr (G.KB + BitVec.ofNat 32 (arr G.w j)), 4 * (G.w + 2)⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr] (s.withRegions (s.rd ++ [G.rs o n]) [G.rK]) t) ?_ ?_
  · unfold loadS
    refine WP.seq (scr_ok (s := s.withRegions (s.rd ++ [G.rs o n]) [G.rK]) (o := o) (d := .r4) h.r8 rfl l (by omega)
      fun s₁ v₁ R₁ M₁ => wp_movw fun s₂ u₂ => WP.block_nil ?_)
    unfold VG.Impl.Rsa.Arm.CrtValues.load
    have hw₁ := (hw.rest R₁).of_upd u₂ (by decide) (by decide) (by decide)
    refine WP.seq (ptr_ok hw₁ (r := .r0) (by decide) (by simp only [nArrs] at hj; omega) fun s₃ p₃ R₃ m₃ hw₃ => ?_)
    refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
    have mem6 : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, M₁]; rfl
    have R₆ : Rest [.r0, .r3, .r4, .r5, .r6, .r12, .lr] (s.withRegions (s.rd ++ [G.rs o n]) [G.rK]) s₆ :=
      (R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans ((R₃.mono (by simp)).trans
        ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp))))))
    have p0 : s₆.gpr .r0 = G.KB + BitVec.ofNat 32 (arr G.w j) := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), p₃]
    have p4 : s₆.gpr .r4 = G.scr + BitVec.ofNat 32 o := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), R₃.gpr _ (by decide),
        u₂.other _ (by decide), v₁]
    refine WP.mono (VG.Proof.Bignum.Arm.loadBE_ok s₆ (src := G.scr + BitVec.ofNat 32 o)
      (dst := G.KB + BitVec.ofNat 32 (arr G.w j)) (n := G.w + 2) (k := n) hn0 (by omega) (by omega)
      (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega)
      (by rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]; omega)
      ⟨G.rs o n, List.mem_append_left _ (by rw [R₆.rd]; simp), by rw [as]; exact Region.contains_self _ _⟩
      ⟨G.rK, by rw [R₆.wr]; exact List.mem_singleton_self _, by
        rw [ad]; exact Offset.contains_base (State.addr G.KB) (by omega) (by omega)⟩
      (by rw [as, ad, e]; exact gi.sdisj (.inl (by omega)) (by omega) (by omega))
      p0 p4 (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, p₃])
      (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), R₃.gpr _ (by decide),
        u₂.gpr, setWidth_ofNat16 (by omega)])
      (by rw [u₆.other _ (by decide), u₅.gpr, dpVal, u₄.other _ (by decide), R₃.gpr _ (by decide),
        u₂.other _ (by decide), R₁.gpr _ (by decide), hw.r9, BitVec.ofNat_add]; rfl)
      (by rw [u₆.gpr])) ?_
    rintro t ⟨v, f, r⟩
    refine ⟨?_, ?_, (R₆.mono (by simp)).trans (r.mono (by simp))⟩
    · rw [v, mem6, as, b]
    · rw [← mem6]; exact f
  · intro t ⟨v, f, R⟩ hr hw' fK
    simp only [State.withRegions_mem] at v
    rw [ad] at v f
    have k : Keep G.KB G.w [j] [] s.mem t.mem := VG.Proof.Rsa.Arm.CrtValues.Keep.of_frame_arr f (by omega)
    rw [VG.Proof.Rsa.Arm.CrtValues.val32_off, Nat.add_zero] at v
    have lt : Spec.Rsa.os2ip bs < 2 ^ (32 * G.w) := by
      have := VG.Proof.Dsa.decodeBE_lt bs
      rw [hn, VG.Proof.Dsa.decodeBE_os2ip] at this
      refine Nat.lt_of_lt_of_le this ?_
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have vw : num t.mem G.KB G.w j = Spec.Dsa.decodeBE bs := by
      rw [VG.Proof.Dsa.decodeBE_os2ip, ← v]
      exact VG.Proof.Rsa.Arm.CrtValues.val32_low2 (by rw [v]; exact lt)
    have R' : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r12, .lr] s t := ⟨R.gpr, hr, hw', R.sp⟩
    exact ⟨⟨h.of_op R' fK hj k vw, x⟩, top_of_lt (by rw [v]; exact lt)⟩

end

end VG.Proof.Dsa.Arm.Gen
