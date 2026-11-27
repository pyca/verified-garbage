module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrTab
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
meta import VerifiedGarbage.Proof.RsaKeyGen.Slots
meta import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWit
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWit
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaKeyGen.AArch64.CTMrWit`, which this module and modules that import it used -/

section

/-!
# A candidate on AArch64: constant time of Miller–Rabin's witness

`mrWitness`, for runs that agree on the working space, `rand` and the
octets read (`mrWitness_ct`): the block before `loadBE` pins its pointers
and count (`witBlk_ok`), the block before the comparison is split after
`ws`, and the forcing block runs from the registers the comparison keeps.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

/-- The public data of a witness: the working space, `rand` and the octets
read. -/
structure WPub where
  L : WsP
  rP : Addr
  u : Nat

/-- Before the witness. -/
def WA (p : WPub) (s : State) : Prop :=
  Ws s p.L.B p.L.Z p.L.w ∧ word s.mem p.L.B (8 * kRand) = p.rP ∧
    word s.mem p.L.B (8 * kUsed) = BitVec.ofNat 64 p.u ∧ word s.mem p.L.B (8 * kLen) = BitVec.ofNat 64 (8 * p.L.w) ∧
    ∃ bs, Src s p.L.B p.L.Z (p.rP + BitVec.ofNat 64 p.u) bs ∧ bs.length = 8 * p.L.w

/-- The registers `loadBE` needs. -/
def wbVal (B rp : Addr) (w u : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x8 => off B (slot w aX)
  | .x1 => rp + BitVec.ofNat 64 u
  | _ => BitVec.ofNat 64 (8 * w)

/-- The block before `loadBE`. -/
theorem witBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {rp : Addr} {u : Nat}
    (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) :
    WP isa (.block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
      ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed])) s fun t =>
      ∀ r ∈ [Reg.x0, .x8, .x1, .x2], t.gpr r = wbVal B rp w u r := by
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₂ ⟨⟨_, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok aX .x8 ((k₂.gpr .x0 (by decide)).trans h.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x3, .x2] (Q := fun t => t.gpr .x1 = rp + BitVec.ofNat 64 u ∧
        t.gpr .x2 = BitVec.ofNat 64 (8 * w)) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h.x0
          have hs₃ := h.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_using [hi, this])
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by have := h.h256; simp only [kUsed, sFn]; omega_using [this]),
            hR, hU, hK])
        (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h1, h2⟩, k₄⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (((k₂.trans k₃).trans k₄).gpr .x0 (by decide)).trans h.x0
        · exact (k₄.gpr .x8 (by decide)).trans h8
        · exact h1
        · exact h2))

theorem zeroAX_ct : RelCT isa (Two WA) (zeroA aX) (Two WA) := by
  have e : zeroA aX = .seq (.block (ws ++ (base aX .x8 ++ [movi .x7 0]))) zeroAcc := by
    simp only [zeroA, List.append_assoc]
  rw [e]
  refine ws_ct (fun p : WPub => p.L.B) (fun p : WPub => p.L.Z) (fun p : WPub => p.L.w) (fun _ _ h => h.1) (by taint_decide)
    fun p s h => ?_
  rw [← e]
  obtain ⟨hw, hR, hU, hK, bs, hsrc, hbl⟩ := h
  have hn := hw.scr.nowrap
  have sX := hw.sl (show aX < 16 by decide)
  refine WP.mono (zeroA_ok hw (show aX < 16 by decide)) fun t ⟨_, o, _, _, _, k⟩ => ?_
  have f : Frm p.L.B [(slot p.L.w aX, 8 * (p.L.w + 2))] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
  have hh : ∀ i < 32, word t.mem p.L.B (8 * i) = word s.mem p.L.B (8 * i) := fun i hi =>
    f.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot p.L.w aX hi)) (by omega_using [hi])
  exact ⟨hw.congr' f (by msb_mut) k (by decide), (hh _ (by decide)).trans hR, (hh _ (by decide)).trans hU,
    (hh _ (by decide)).trans hK, bs, hsrc.congrK (InScr.of_frm f (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact sX)) k, hbl⟩

/-- The octets into `aX`. -/
theorem witLoad_ct : RelCT isa (Two WA) (seqs [zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand,
    ldh .x3 kUsed, .add .x .x1 .x1 .x3, ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE])
    (Two fun (p : WPub) t => Ws t p.L.B p.L.Z p.L.w) :=
  two_post (RelCT.seq zeroAX_ct (RelCT.seq (two_piece (Ψ := fun p t => ∀ r ∈ [Reg.x0, .x8, .x1, .x2],
      t.gpr r = wbVal p.L.B p.rP p.L.w p.u r) [.x0]
      (pins_ws' (fun p : WPub => p.L.B) (fun p : WPub => p.L.Z) (fun p : WPub => p.L.w) fun _ _ h => h.1)
      (by taint_decide)
      fun _ _ ⟨hw, hR, hU, hK, _⟩ => witBlk_ok hw hR hU hK)
    (two_taint _ (pins_of _ (fun p => wbVal p.L.B p.rP p.L.w p.u) fun _ _ h => h) (by taint_decide))))
    fun _ _ ⟨hw, hR, hU, hK, bs, hsrc, hbl⟩ =>
      WP.mono (witLoad_ok hw hR hU hK hsrc hbl) fun _ ⟨_, _, _, h, _⟩ => h

/-- After the low words' test. -/
def WL (p : WPub) (s : State) : Prop :=
  Ws s p.L.B p.L.Z p.L.w ∧ (s.gpr .x5 = 0 ↔ wv s.mem p.L.B (slot p.L.w aX) p.L.w ≤ 1)

theorem witLow_ct : RelCT isa (Two fun (p : WPub) t => Ws t p.L.B p.L.Z p.L.w)
    (seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]]) (Two WL) :=
  ws_ct (fun p : WPub => p.L.B) (fun p : WPub => p.L.Z) (fun p : WPub => p.L.w) (fun _ _ h => h) (by taint_decide)
    fun _ s h => WP.mono (witLow_ok h) fun t ⟨hl, hm, k⟩ =>
      ⟨h.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide), by rw [hm]; exact hl⟩

/-- The block before the comparison, up to `ws`. -/
theorem witGeWs_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++
      ws)) s fun t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal B w r := by
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x7, .x8, .x4, .x3, .x9] (Q := fun t => t.mem = s.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm, k⟩ => ?_)
  exact ws_pin (h.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide))

theorem witCmp_eq : (.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4,
    .csel .x .x9 .x8 .x7] ++ ws ++ base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4,
    ld .x4 .x17, .subs .x .x3 .x3 .x4, next .x16, next .x17, .subImm .x .x14 .x12 1]) : Prog isa) =
    .block (([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws) ++
      (base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1])) := by
  simp only [List.append_assoc]

/-- The comparison with `c`. -/
theorem witCmp_ct : RelCT isa (Two WL)
    (seqs [.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++
      ws ++ base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17,
      .subs .x .x3 .x3 .x4, next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop])
    (Two fun (p : WPub) t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal p.L.B p.L.w r) := by
  show RelCT isa _ (.seq _ cmpLoop) _
  rw [witCmp_eq]
  refine RelCT.block_seq (pin_ct [.x0] [.x0, .x12, .x11] (fun p : WPub => wsVal p.L.B p.L.w)
    (pins_ws' (fun p : WPub => p.L.B) (fun p : WPub => p.L.Z) (fun p : WPub => p.L.w) fun _ _ h => h.1)
      (by taint_decide)
    (fun _ _ h => witGeWs_ok h.1) (by taint_decide) fun p s ⟨hw, hl⟩ => ?_)
  refine WP.block_seq_iff.mp ?_
  rw [← witCmp_eq]
  exact WP.mono (witCmp_ok hw rfl hl) fun t ⟨_, _, _, _, h12, h11, _, k⟩ =>
    wsVal_of ((k.gpr .x0 (by decide)).trans hw.x0) h12 h11

/-- The witness leaks the same in runs that agree on the working space,
`rand` and the octets read. -/
theorem mrWitness_ct : RelCT isa (Two WA) (seqs mrWitness) fun _ _ => True := by
  rw [mrWitness_eq]
  exact ct_app' (by simp) (by simp) witLoad_ct (ct_app' (by simp) (by simp) witLow_ct
    (ct_app' (by simp) (by simp) witCmp_ct (two_taint _ (pins_of _ (fun p : WPub => wsVal p.L.B p.L.w)
      fun _ _ h => h) (by taint_decide))))

end VG.Proof.RsaKeyGen.AArch64

end

end

/-!
# A candidate on AArch64: constant time of a round of Miller–Rabin

A round, from what it needs (`R0`), for runs that agree on the
working space, `rand`, the octets read and whether the witness passes
(`RP`): the witness (`mrWitness_ct`), its Montgomery form, the table and
`y := 1` (`tabBuild_ct`), the exponentiation (`mrExpLoop_ct`), and the
end, which branches on the flag (`roundTail_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

/-- The public data of a round: the working space, `rand`, the octets read
and whether the witness passes. -/
structure RP where
  L : WsP
  rP : Addr
  u : Nat
  pass : Bool

/-- What a round needs. -/
def R0 (p : RP) (s : State) : Prop :=
  4 ≤ p.L.w ∧ p.L.w ≤ 128 ∧ slot p.L.w aE + 8 * (p.L.w + 2) ≤ p.L.Z ∧
    ∃ (c bm : Nat) (r : List Byte) (i uni ch : Nat), MrCtx s p.L.B p.L.Z p.L.w c bm ∧ ECtx s.mem p.L.B p.L.w c ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) * 2 ^ (64 * p.L.w) % c ∧ 1 < c ∧
    VG.Proof.RsaKeyGen.PrimeShape (64 * p.L.w) c ∧ word s.mem p.L.B (8 * kRand) = p.rP ∧
    word s.mem p.L.B (8 * kUsed) = BitVec.ofNat 64 p.u ∧ word s.mem p.L.B (8 * kLen) = BitVec.ofNat 64 (8 * p.L.w) ∧
    Src s p.L.B p.L.Z p.rP r ∧ p.u + 8 * p.L.w ≤ r.length ∧ word s.mem p.L.B (8 * kI) = BitVec.ofNat 64 i ∧
    word s.mem p.L.B (8 * kUni) = BitVec.ofNat 64 uni ∧ word s.mem p.L.B (8 * kChecks) = BitVec.ofNat 64 ch ∧
    i < 2 ^ 61 ∧ uni < 2 ^ 61 ∧ ch < 2 ^ 62 ∧ passOf c p.L.w p.u r = p.pass

theorem r0_wa {p : RP} {s : State} (h : R0 p s) : WA ⟨p.L, p.rP, p.u⟩ s := by
  obtain ⟨-, -, -, c, bm, r, i, uni, ch, hc, -, -, -, -, hR, hU, hK, hsrc, hlen, -⟩ := h
  exact ⟨hc.ws, hR, hU, hK, _, Src.seg hsrc hlen, by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]⟩

/-- After the witness: `c`, `-c⁻¹` and `R² mod c`. -/
def P1 (p : RP) (s : State) : Prop :=
  4 ≤ p.L.w ∧ p.L.w ≤ 128 ∧ slot p.L.w aE + 8 * (p.L.w + 2) ≤ p.L.Z ∧ ∃ c bm, MrCtx s p.L.B p.L.Z p.L.w c bm ∧
    c % 2 = 1 ∧ 1 < c ∧ wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) * 2 ^ (64 * p.L.w) % c

theorem witP1_ct : RelCT isa (Two R0) (seqs mrWitness) (Two P1) := by
  refine two_post (two_map (fun p : RP => (⟨p.L, p.rP, p.u⟩ : WPub)) (fun _ _ h => r0_wa h) mrWitness_ct) ?_
  rintro p s ⟨h4, h128, hEZ, c, bm, r, i, uni, ch, hc, -, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, -⟩
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [h4]) hsh
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have sR2 : slot p.L.w aR2 + 8 * (p.L.w + 2) ≤ p.L.Z := by
    have := slot_lt (w := p.L.w) (show aR2 < 16 by decide); omega_using [hZ, this]
  refine WP.mono (mrWitness_ok hc h4 h128 hsh.1 hb hR hU hK (Src.seg hsrc hlen) (by
      simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun t ⟨hc', _, _, _, hf, _⟩ => ⟨h4, h128, hEZ, c, bm, hc', hsh.1, hc1, ?_⟩
  rw [hf.wv_eq (d := slot p.L.w aR2) (k := p.L.w) (by rd_disj) (by omega_using [hn, sR2]), hR2]

theorem preMul_ok (M : Mont) {p : RP} {s : State} (h : P1 p s) : WP isa (M.mm aXm aX aR2) s (TB p.L) := by
  obtain ⟨h4, h128, hEZ, c, bm, hc, hodd, hc1, hR2⟩ := h
  have hg := hc.good
  have hn := hc.ws.scr.nowrap
  have hRc : Nat.Coprime (2 ^ (64 * p.L.w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  refine WP.mono (M.mm_ok hg.1 hg.2 (by omega_using [h4]) (by omega_using [h128]) (o := aXm) (a := aX) (b := aR2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hR2, hc.n]; exact Nat.mod_lt _ (by omega_using [hodd]))) fun t ⟨_, hlt, hy, ha, k⟩ => ?_
  rw [hc.n] at hlt hy
  rw [hR2] at hy
  have hf : Frm p.L.B [(slot p.L.w aAcc, 8 * (p.L.w + 2)), (slot p.L.w aTmp, 8 * (p.L.w + 2)),
      (slot p.L.w aXm, 8 * (p.L.w + 2))] s.mem t.mem := Frm.of_arrays ha (by simp)
  refine ⟨h4, h128, hEZ, c, bm, wv s.mem p.L.B (slot p.L.w aX) p.L.w,
    hc.of_frm hf (by kmut) k (by decide) ((VG.Proof.RsaKeyGen.mm_shape _ _).hdrW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl), hodd, hc1, ?_⟩
  rw [VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_mul_mod, ← Nat.mod_eq_of_lt hlt]
  refine VG.Proof.Bignum.mont_cancel hRc ?_
  rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]

theorem preMul_ct (M : Mont) : RelCT isa (Two P1) (M.mm aXm aX aR2) (Two fun (p : RP) t => TB p.L t) :=
  two_post (two_map (fun p : RP => p.L) (fun _ _ ⟨_, _, _, _, _, hc, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) fun _ _ h => preMul_ok M h

theorem copyB_ct : RelCT isa (Two fun (p : RP) t => TB p.L t) (copyA aB aXm) (Two fun (p : RP) t => TB p.L t) := by
  have e : copyA aB aXm = .seq (.block (ws ++ (base aXm .x16 ++ base aB .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  refine ws_ct (fun p : RP => p.L.B) (fun p : RP => p.L.Z) (fun p : RP => p.L.w) (fun _ _ h => h.ws) (by taint_decide)
    fun p s h => ?_
  rw [← e]
  obtain ⟨h4, h128, hEZ, c, bm, b, hc, hodd, hc1, hX⟩ := h
  have hn := hc.ws.scr.nowrap
  have sB := hc.ws.sl (show aB < 16 by decide)
  have sX := hc.ws.sl (show aXm < 16 by decide)
  refine WP.mono (copyA_ok hc.ws (o := aB) (a := aXm) (by decide) (by decide) (by decide)) fun t ⟨hv, o, _, _, k⟩ => ?_
  have f : Frm p.L.B [(slot p.L.w aB, 8 * (p.L.w + 2))] s.mem t.mem :=
    Frm.of_outside (o.mono (o' := slot p.L.w aB) (n' := 8 * (p.L.w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  exact ⟨h4, h128, hEZ, c, _, b, hc.setB f (by kmut) k (by decide) ((VG.Proof.RsaKeyGen.arr_shape _ _).hdrW rfl rfl) ((VG.Proof.RsaKeyGen.arr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.arr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.arr_shape _ _).apartW rfl rfl) rfl,
    hodd, hc1, by rw [f.wv_eq (d := slot p.L.w aXm) (k := p.L.w) ((VG.Proof.RsaKeyGen.arr_shape _ _).apartW rfl rfl) (by omega_using [hn, sX])]; exact hX⟩

/-- After the exponentiation: the flag, the witness passing or not. -/
def Rmid (p : RP) (s : State) : Prop := Ws s p.L.B p.L.Z p.L.w ∧ word s.mem p.L.B (8 * kFlag) = mask p.pass

theorem mask_beq (b : Bool) : (mask b == 0) = !b := by cases b <;> decide

/-- The end of a round. -/
theorem roundTail_ct : RelCT isa (Two Rmid) (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 3, sth .x3 kStat])
        (.block [ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1, .logic .and .x .x4 .x4 .x5,
          ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni,
          movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5, .csel .x .x13 .x10 .x9, ldh .x5 kChecks,
          .subs .x .x6 .x4 .x5, .csel .x .x13 .x13 .x9, sth .x13 kStat])]) fun _ _ => True := by
  have pw : ∀ {Φ : RP → State → Prop}, (∀ p s, Φ p s → Ws s p.L.B p.L.Z p.L.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun p : RP => p.L.B) (fun p : RP => p.L.Z) (fun p : RP => p.L.w) h
  refine RelCT.seq (two_piece (Ψ := fun p t => Ws t p.L.B p.L.Z p.L.w ∧
      isa.eval (.zero .x .x3) t = some (!p.pass)) [.x0] (pw fun _ _ h => h.1) (by taint_decide)
    fun p s ⟨hw, hF⟩ => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide))
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide)))
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask p.pass ∧ t.mem = s.mem) (by
    brun [hw.x0, hdr_enc (show kFlag < 32 by decide), hw.scr.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega_using [h256]),
      hF]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · exact hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)
  · rw [eval_zero, h3, mask_beq]

end VG.Proof.RsaKeyGen.AArch64
