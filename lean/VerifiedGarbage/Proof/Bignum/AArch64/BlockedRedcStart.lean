module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCancelTile
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

abbrev startRegs := VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nn ++ VG.Impl.Bignum.AArch64.BlockedRedc.tt ++
  [.x1, .x27, .x15, .x17]

def startBlock : List Instr := VG.Impl.Bignum.AArch64.BlockedRedc.asLoad ++
  [ldh .x17 (sArr Public.aN), ldh .x15 sMinv] ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad ++
  (List.range 8).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.cancel

theorem startHeader_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 256 ≤ Z) :
    WP isa (.block [ldh .x17 (sArr Public.aN), ldh .x15 sMinv]) s fun t =>
      (t.gpr .x17 = word s.mem B (8 * sArr Public.aN) ∧
       t.gpr .x15 = word s.mem B (8 * sMinv) ∧ t.mem = s.mem) ∧
      Keep [.x17, .x15] s t := by
  refine WP.keep [.x17, .x15] ?_ rfl rfl rfl
  brun [h0, hs.ld (show 8 * sArr Public.aN + 8 ≤ Z by unfold sArr Public.aN; omega),
    hs.ld (show 8 * sMinv + 8 ≤ Z by unfold sMinv; omega)]

/-- The first block produces all eight reduction coefficients. The frame
holds for every inverse; its arithmetic relation requires a valid inverse. -/
theorem startBlock_ok {s : State} {B : Addr} {Z eQ eN : Nat} {inv : Word}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h8 : s.gpr .x8 = off B eQ)
    (h7 : s.gpr .x7 = 0) (hZ : 256 ≤ Z) (hQ : eQ + 64 ≤ Z) (hN : eN + 64 ≤ Z)
    (hQN : eQ + 64 ≤ eN ∨ eN + 64 ≤ eQ)
    (hn : word s.mem B (8 * sArr Public.aN) = off B eN)
    (hi : word s.mem B (8 * sMinv) = inv) :
    WP isa (.block startBlock) s fun t =>
      (((word s.mem B eN).toNat * inv.toNat + 1) % 2 ^ 64 = 0 →
        (2 ^ 64) ^ 8 * blockValue (accumulator t) =
          wv s.mem B eQ 8 + wv t.mem B eQ 8 * wv s.mem B eN 8) ∧
      Outside B eQ 64 s.mem t.mem ∧ t.gpr .x17 = off B eN ∧
      Keep startRegs s t := by
  rewrite [startBlock, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (asLoad_ok hs h8 hQ) fun a ⟨⟨hav, ham, _⟩, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (startHeader_ok (hs.congr ka.wr) ((ka.gpr .x0 (by decide)).trans h0) hZ)
    fun b ⟨⟨hb17, hb15, hbm⟩, kb⟩ => ?_
  have kab := ka.trans kb
  have h17 : b.gpr .x17 = off B eN := hb17.trans
    ((congrArg (fun m : Mem => word m B (8 * sArr Public.aN)) ham).trans hn)
  have h15 : b.gpr .x15 = inv := hb15.trans
    ((congrArg (fun m : Mem => word m B (8 * sMinv)) ham).trans hi)
  apply WP.block_append
  refine WP.mono (nsLoad_ok (hs.congr kab.wr) h17 hN) fun d ⟨⟨hdn, hdm, _⟩, kd⟩ => ?_
  have kad := kab.trans kd
  have dm := hdm.trans (hbm.trans ham)
  have d17 := (kd.gpr .x17 (by decide)).trans h17
  have d15 := (kd.gpr .x15 (by decide)).trans h15
  refine WP.mono (cancelPrefix_ok (hs.congr kad.wr)
    ((kad.gpr .x8 (by decide)).trans h8) d17 ((kad.gpr .x7 (by decide)).trans h7)
    hQ (by omega) (by omega) (Nat.le_refl 8)) fun t hI => ?_
  have hA := (congrArg blockValue (keep_accumulator (kb.trans kd) (by decide))).trans
    ((blockValue_congr hav).trans (blockValue_words s.mem B eQ))
  have hn0 := congrArg (fun m : Mem => word m B eN) hdm
  have hNV : blockValue (operand d (word d.mem B eN)) = wv s.mem B eN 8 :=
    (congrArg (fun n => blockValue (operand d n)) hn0).trans
      ((blockValue_congr hdn).trans ((blockValue_words b.mem B eN).trans
        (congrArg (fun m : Mem => wv m B eN 8) (hbm.trans ham))))
  refine ⟨?_, ?_, (hI.keep.gpr .x17 (by decide)).trans d17,
    (kad.trans hI.keep).mono (by decide)⟩
  · intro hInv
    have dN := congrArg BitVec.toNat (congrArg (fun m : Mem => word m B eN) dm)
    have dI := congrArg BitVec.toNat d15
    have hInvD : ((word d.mem B eN).toNat * (d.gpr .x15).toNat + 1) % 2 ^ 64 = 0 :=
      ((congrArg (fun n => (n * (d.gpr .x15).toNat + 1) % 2 ^ 64) dN).trans
        (congrArg (fun i => ((word s.mem B eN).toNat * i + 1) % 2 ^ 64) dI)).trans hInv
    have hv := hI.value hInvD
    have hr : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
    have hp := congrArg (fun r : Nat => r * blockValue (accumulator t)) hr
    exact hp.symm.trans (hv.trans ((congrArg (· + wv t.mem B eQ 8 *
      blockValue (operand d (word d.mem B eN))) hA).trans
        (congrArg (fun n => wv s.mem B eQ 8 + wv t.mem B eQ 8 * n) hNV)))
  · intro x hx
    exact (hI.frame x hx).trans (congrArg (fun m : Mem => m x) dm)

end VG.Proof.Bignum.AArch64.BlockedRedc
