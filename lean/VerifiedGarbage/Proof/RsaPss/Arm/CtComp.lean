module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Rc2.Memory

/-!
# RSASSA-PSS on ARMv7: hashing, every block compressed

`comp_vp`: one compression of a block of `Y` into the hash value at `oSt`.
`compLoop_vp`: every one of `Y`'s `nbm` blocks compressed, and the hash
value after block `lb` (the last of the padded message, `⌊(ℓ + L) / B⌋`)
selected into `oSel`: it is that of `Y`'s first `lb + 1` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.MdStream (Md)

/-- `Y`'s first `T` bytes, as a list. -/
def ylist (yv : Nat → Byte) (T : Nat) : List Byte := (List.range T).map yv

theorem ylist_getD {yv : Nat → Byte} {T j : Nat} (h : j < T) : (ylist yv T).getD j 0 = yv j := by
  simp [ylist, List.getD_eq_getElem?_getD, h]

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The regions a compression writes. -/
abbrev compW (scr : BitVec 32) : List Region := [sR scr oSt h.N, sR scr oCW h.H.md.so]

/-- One compression of the block at `src` (an offset `o` of our part of
`scratch`) into the hash value at `oSt`, with the working space at `oCW`. -/
theorem comp_vp (hg : Geo L scr) {o : Nat} (ho : oY ≤ o) (ho' : o + h.B ≤ oRsa) {X : State → Mem → Prop} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ s.gpr .r3 = scr ∧
        s.gpr .r6 = scr + BitVec.ofNat 32 o)
      h.H.md.compressBlock
      (fun σ s => Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame (compW h scr) m₀ s.mem ∧
        h.md.stateAt s.mem (sa scr oSt) = h.md.compress (h.md.stateAt m₀ (sa scr oSt)) (h.md.blockAt m₀ (sa scr o))) := by
  have hN := h.N_le
  have hso := h.so_le
  have hB := h.B_le
  have hB64 := h.B_ge
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  have aSt : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by decide)
  have aO : State.addr (scr + BitVec.ofNat 32 o) = sa scr o := hg.addr (by pomega)
  have a0 : State.addr scr = sa scr oCW := by simp [sa, oCW]
  have callOk : ∀ σ s, Ctx L scr σ s → s.gpr .r0 = scr + BitVec.ofNat 32 oSt → s.gpr .r3 = scr →
      s.gpr .r6 = scr + BitVec.ofNat 32 o →
      Pbkdf2.Md.Arm.CallOk s h.N h.B h.H.md.so (scr + BitVec.ofNat 32 oSt) scr (scr + BitVec.ofNat 32 o) := by
    intro σ s hc r0 r3 r6
    refine ⟨r0, r3, r6, by rw [hg.scr_lt (by decide)]; pomega, by rw [hg.scr_lt (by pomega)]; pomega,
      by pomega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [aSt, a0]; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [aO, aSt]; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [aO, a0]; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [aO, aSt, a0]
      refine Covers.cons (Covers.one (hg.rd hc.st (by pomega))) (Covers.cons (Covers.one (hg.rd hc.st (by pomega)))
        (Covers.cons (Covers.one (hg.rd hc.st (by pomega))) Covers.nil))
    · rw [aSt, a0]
      exact Covers.cons (Covers.one (hg.wr hc.st (by pomega))) (Covers.cons (Covers.one (hg.wr hc.st (by pomega)))
        Covers.nil)
  refine VP.of_ct (fun _ _ => Pbkdf2.Md.Arm.compressBlock_rel (H := h.md) h.ok.comp fun a b hab =>
    ⟨callOk _ _ hab.1.1 hab.1.2.2.1 hab.1.2.2.2.1 hab.1.2.2.2.2,
      callOk _ _ hab.2.1 hab.2.2.2.1 hab.2.2.2.2.1 hab.2.2.2.2.2⟩) fun σ s ⟨hc, hx, r0, r3, r6⟩ => ?_
  refine Pbkdf2.Md.Arm.compressBlock_ok (H := h.md) h.ok.comp (callOk σ s hc r0 r3 r6)
    fun s' rd wr _ _ _ sp fr e => ?_
  rw [aSt, a0] at fr
  rw [aSt, aO] at e
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, s.mem, hx, fr, e⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by pomega)
    · exact hg.inW (by pomega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.slot ok (by pomega) (by rw [hg.F]; decide)
    · exact hg.slot ok (by pomega) (by rw [hg.F]; decide)

end VG.Proof.RsaPss.Arm
