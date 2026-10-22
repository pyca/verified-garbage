module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomFrame
import VerifiedGarbage.Proof.Dsa.Arm.Env
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Copying bytes under a mask (32-bit ARM)

`copyMasked_ok`: `Generate.copyMasked` copies `n > 0` bytes from `r1` to
`r10`, each and-ed with the mask in `r3`, leaving `r10` past them; it writes
only those bytes.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_dp wp_ldrb wp_strb op2_reg eval_ne ofNat_beq_zero dpVal)

/-- A byte under a mask. -/
abbrev masked (mask : BitVec 32) (b : Byte) : Byte := (b.setWidth 32 &&& mask).setWidth 8

/-- The copy after its first `k` bytes. -/
structure CopyMaskInv (s : State) (src dst : BitVec 32) (bs : List Byte) (mask : BitVec 32) (k : Nat)
    (t : State) : Prop where
  r1 : t.gpr .r1 = src + BitVec.ofNat 32 k
  r10 : t.gpr .r10 = dst + BitVec.ofNat 32 k
  r2 : t.gpr .r2 = BitVec.ofNat 32 (bs.length - k)
  r3 : t.gpr .r3 = mask
  bytes : ∀ i < k, t.mem (State.addr dst + BitVec.ofNat 64 i) = masked mask (bs.getD i 0)
  out : Outside (State.addr dst) 0 bs.length s.mem t.mem
  rest : Rest [.r0, .r1, .r2, .r10] s t

/-- Where the copy goes: writable bytes below `2³²`, apart from the source. -/
structure CopyDst (s : State) (src dst : BitVec 32) (n : Nat) : Prop where
  fit : dst.toNat + n ≤ 2 ^ 32
  wr : ∀ i < n, InRegions s.wr (State.addr dst + BitVec.ofNat 64 i) 1
  apart : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩

theorem copyStep_ok {s t : State} {src dst : BitVec 32} {bs : List Byte} {mask : BitVec 32} {k : Nat}
    (hin : BytesIn s src bs) (D : CopyDst s src dst bs.length) (hn : bs.length < 2 ^ 16) (hk : k < bs.length)
    (I : CopyMaskInv s src dst bs mask k t) :
    WP isa (.block Generate.copyStep) t fun u => CopyMaskInv s src dst bs mask (k + 1) u ∧
      u.z = decide (bs.length - (k + 1) = 0) := by
  have hfit := hin.fit
  have dfit := D.fit
  have hlt : bs.length < 2 ^ 32 := by omega
  -- The source byte, apart from what the copy wrote.
  have src_ofs : ofs (State.addr src) (State.addr src + BitVec.ofNat 64 k) = k := by
    have := ofs_off (State.addr src) (d := 0) (i := k) (by omega)
    rwa [off, BitVec.add_zero, Nat.zero_add] at this
  have keep : t.mem (State.addr src + BitVec.ofNat 64 k) = bs[k] := by
    rw [I.out _ (.inr (by rw [Nat.zero_add]; exact ofs_apart D.apart.symm (by omega))), hin.val k hk]
  unfold Generate.copyStep
  refine wp_ldrb (a := State.addr src + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, I.r1, VG.Arm.addr_add (by omega)])
    (by rw [I.rest.rd, I.rest.wr]; exact hin.rd k hk) fun t₁ u₁ => ?_
  rw [keep] at u₁
  refine wp_dp (op2_reg _ _) fun t₂ u₂ => ?_
  refine wp_strb (a := State.addr dst + BitVec.ofNat 64 k) (by decide)
    (by rw [BitVec.add_zero, u₂.other _ (by decide), u₁.other _ (by decide), I.r10, VG.Arm.addr_add (by omega)])
    (by rw [u₂.wr, u₁.wr, I.rest.wr]; exact D.wr k hk) fun t₃ u₃ => ?_
  refine wp_inc fun t₄ u₄ => wp_inc fun t₅ u₅ => wp_dec fun t₆ u₆ z₆ => WP.block_nil ?_
  have r3 : t₂.gpr .r3 = mask := by rw [u₂.other _ (by decide), u₁.other _ (by decide), I.r3]
  have v₂ : t₂.gpr .r0 = (bs[k]).setWidth 32 &&& mask := by
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other _ (by decide), I.r3]
  have m₆ : t₆.mem = t.mem.writeW (State.addr dst + BitVec.ofNat 64 k) (masked mask bs[k]) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v₂, u₂.mem, u₁.mem]
  have R : Rest [.r0, .r1, .r2, .r10] t t₆ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest _).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  have r2 : t₆.gpr .r2 = BitVec.ofNat 32 (bs.length - (k + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), I.r2, ofNat_sub_one (by omega), show bs.length - k - 1 = bs.length - (k + 1) by omega]
  have dst_ofs : ∀ i, i < bs.length →
      ofs (State.addr dst) (State.addr dst + BitVec.ofNat 64 i) = i := fun i hi => by
    have := ofs_off (State.addr dst) (d := 0) (i := i) (by omega)
    rwa [off, BitVec.add_zero, Nat.zero_add] at this
  have O : Outside (State.addr dst) 0 bs.length t.mem t₆.mem := by
    rw [m₆]
    have := writeW8_outside t.mem (State.addr dst) (d := k) (masked mask bs[k]) (by omega)
    simp only [off] at this
    exact this.mono (by omega) (by omega)
  refine ⟨⟨?_, ?_, r2, ?_, fun i hi => ?_, I.out.trans O, I.rest.trans R⟩, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      I.r1, Offset.add_ofNat_add_one]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), I.r10, Offset.add_ofNat_add_one]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, r3]
  · rw [m₆]
    by_cases hik : i = k
    · subst hik
      rw [writeW8_self, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    · rw [(writeW8_outside t.mem (State.addr dst) (d := k) (masked mask bs[k]) (by omega)) _
        (by rw [dst_ofs i (by omega)]; omega)]
      exact I.bytes i (by omega)
  · rw [z₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      I.r2, ofNat_sub_one (by omega), show bs.length - k - 1 = bs.length - (k + 1) by omega,
      ofNat_beq_zero (by omega)]

theorem copyMasked_ok {s : State} {src dst : BitVec 32} {bs : List Byte} {mask : BitVec 32}
    (hin : BytesIn s src bs) (D : CopyDst s src dst bs.length) (hn : bs.length < 2 ^ 16) (h0 : 0 < bs.length)
    (I : CopyMaskInv s src dst bs mask 0 s) :
    WP isa Generate.copyMasked s fun u => CopyMaskInv s src dst bs mask bs.length u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) =>
      ∃ j, n = bs.length - j ∧ j < bs.length ∧ CopyMaskInv s src dst bs mask j u)
    (fun n u hu => ?_) bs.length s ⟨0, by omega, h0, I⟩
  obtain ⟨j, hnj, hj, J⟩ := hu
  refine WP.mono (copyStep_ok hin D hn hj J) fun v ⟨J', z⟩ => ?_
  by_cases he : bs.length - (j + 1) = 0
  · left
    refine ⟨by rw [eval_ne, z, decide_eq_true he]; rfl, ?_⟩
    rw [show bs.length = j + 1 by omega]; exact J'
  · right
    exact ⟨by rw [eval_ne, z, decide_eq_false he]; rfl, bs.length - (j + 1), by omega, j + 1, rfl, by omega, J'⟩

/-- The copied bytes. -/
theorem CopyMaskInv.bytesAt {s t : State} {src dst : BitVec 32} {bs : List Byte} {mask : BitVec 32}
    (I : CopyMaskInv s src dst bs mask bs.length t) :
    Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = bs.map (masked mask) := by
  apply List.ext_getElem
  · simp [Spec.Rsa.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    rw [I.bytes i (by simpa [Spec.Rsa.bytesAt] using h₁), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h₂), Option.getD_some]

end VG.Proof.Dsa.Arm
