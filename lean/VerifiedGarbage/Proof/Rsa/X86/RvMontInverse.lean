module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The negative Montgomery inverse of the public recovery modulus

`KS.setupInverse`: `setupInverse` reads `[mBase]`'s low word through a
pointer to the array, and stores `-m⁻¹ mod 2³²` in the header word `sInv`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.setupInverse (h : KS g s0 A live AW liveW V ls s)
    (hm : mBase ∈ live) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (odd : m % 2 = 1) (slots : ∀ d ∈ ls, d + 4 ≤ sInv ∨ sInv + 4 ≤ d) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.setupInverse) s
      fun t => KS g s0 A live AW liveW V ls t ∧ MR g m t := by
  have positive : 0 < g.n := by have := h.lower; omega
  have header := h.ws.hdr_le
  have nw := h.ws.workspace.nowrap
  have hv : num s.mem g.B g.w mBase = m := (h.arrs mBase hm).trans value
  have kn := kw_nar g.n
  unfold VG.Impl.Rsa.X86.RecoverRt.setupInverse
  simp only [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.lowPtr_ok h.rt (by decide : mBase < nArr) fun u hu K mu p => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (VG.Proof.Rsa.X86.KeyRt.lowSrc hu (by decide) p) fun v Vv _ => ?_
  have low := VG.Proof.Rsa.X86.KeyRt.low_word (B := g.B) (m := u.mem) (j := mBase)
    (w := VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8)) (by rw [kn]; unfold width; omega)
  rw [mu, kn] at low
  have hodd : (v.gpr .ebx).toNat % 2 = 1 := by
    rw [Vv.gpr, mu, kn, ← low, hv, Nat.mod_mod_of_dvd _ (by decide), odd]
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.inverse_ok v hodd) fun x ⟨inv, kx, mx⟩ => ?_)
  have Kx : Keeps opRegs s x :=
    ((K.mono (by decide)).trans (Vv.keeps.mono (by decide))).trans (kx.mono (by decide))
  have hs : Scr x g.B g.Z := h.ws.workspace.of_keeps Kx (by decide)
  refine wp_storeS (hs.ea (by unfold sInv hdr at *; omega)) (hs.write (by unfold sInv hdr at *; omega))
    fun t mt => WP.block_nil ?_
  have ms : x.mem = s.mem := by rw [mx, Vv.mem, mu]
  have frame : Outside g.B sInv 4 s.mem t.mem := by
    rw [mt.mem, ms]
    exact writeW32_outside _ _ _ (by unfold sInv hdr at *; omega)
  have k : Keep g.B g.w [] [sInv] s.mem t.mem := Keep.of_slot frame (by simp)
  have r : Keeps opRegs s t := Kx.trans (mt.keeps [] |>.mono (by decide))
  refine ⟨h.core k (by simp) (by simp [sInv]; decide) r (h.arrs_w k (by simp) (by simp [sInv]; decide)) h.live_lt
    (h.arrsW_w k (by simp) (by simp [sInv]; decide)) h.liveW_lt (h.sl_keep k (by simpa using slots)) h.ls_ok,
    positive, ?_, bound, ?_⟩
  · rw [k.num (by simp) (by decide) (h.ws.fit64 (by decide)), hv]
  · have stored : w32 t.mem g.B sInv = (x.gpr .eax).toNat := by rw [mt.mem, w32_write_self]
    rw [Vv.gpr, mu, kn] at inv
    have lowBound : (s.mem.readW (off g.B (arr g.w mBase)) 32).toNat < 2 ^ 32 :=
      (s.mem.readW (off g.B (arr g.w mBase)) 32).isLt
    have product : m * w32 t.mem g.B sInv % 2 ^ 32 =
        (s.mem.readW (off g.B (arr g.w mBase)) 32).toNat * (x.gpr .eax).toNat % 2 ^ 32 := by
      rw [stored, Nat.mul_mod m, Nat.mul_mod (s.mem.readW _ 32).toNat, ← hv, low,
        Nat.mod_eq_of_lt lowBound]
    rw [Nat.add_mod, product, ← Nat.add_mod]
    exact inv

end
end VG.Proof.Rsa.X86.Recover
