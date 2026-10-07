import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrExp
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound

/-!
# A candidate on AArch64: constant time of Miller–Rabin's witness

`mrWitness`, for runs that agree on the working space, `rand` and the
octets read (`mrWitness_ct`): the block before `loadBE` pins its pointers
and count (`witBlk_ok`), the block before the comparison is split after
`ws`, and the forcing block runs from the registers the comparison keeps.
-/

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
            hs₃.ld (by have := h.h256; omega)
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by have := h.h256; simp only [kUsed, sFn]; omega),
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
      rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot p.L.w aX hi)) (by omega)
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
