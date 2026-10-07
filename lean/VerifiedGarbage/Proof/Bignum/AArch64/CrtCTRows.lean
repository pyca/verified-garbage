import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-!
# RSA with the CRT on AArch64: products in constant time

`zeroAccs` (`zeroAccs_ct`), and a product of an array of `p`'s workspace and
`q`'s `n` into the modulus' accumulators (`rows_ct`), which `pqProduct` and
`finish` make. `rowsHdr` loads each prime's workspace's base from the header
and then its header through it: the taint analysis, to which memory is
secret, checks it in three parts, each from the registers that correctness
pins after the one before.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `acc := 0` over `2 w + 2` words. -/
theorem zeroAccs_ct : RelCT isa (Two GoodW) (seqs zeroAccs) fun _ _ => True := by
  unfold zeroAccs
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x16 = off L.B (slot L.w aAcc) ∧
      t.gpr .x14 = BitVec.ofNat 64 (L.w + L.w + 2)) [.x0] pins_goodW (by taint_decide) fun L s h => ?_)
    (two_taint [.x16, .x14] (pins_of (fun L r => if r = .x16 then off L.B (slot L.w aAcc) else
      BitVec.ofNat 64 (L.w + L.w + 2))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.x7, .x12, .x14, .x16] (Q := fun t => t.gpr .x16 = off L.B (slot L.w aAcc) ∧
      t.gpr .x14 = BitVec.ofNat 64 (L.w + L.w + 2))
    (by brun [hg.x0, hdr_enc (sArr_lt (show aAcc < 8 by decide)), hdr_enc (show sW < 32 by decide),
      hl (sArr aAcc) (by decide), hl sW (by decide), hg.hdr.harr aAcc (by decide), hg.hdr.hw, ofNat_add_ofNat])
    (by decide) (by decide) (by decide +kernel)) fun _ h => h.1

/-- The public data of a product: `n`'s workspace and the primes'. -/
structure RowsPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  oq : Nat
  wp : Nat
  wq : Nat

/-- What `rowsHdr ja` loads (`rowsHdr_ok`'s hypotheses), with `[ja]` at its
base. -/
def RowsPre (ja : Nat) (p : RowsPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ word s.mem p.B (8 * sArr aAcc) = off p.B (slot p.w aAcc) ∧
    word s.mem p.B (8 * Crt.sWsP) = off p.B p.op ∧ word s.mem p.B (8 * Crt.sWsQ) = off p.B p.oq ∧
    word s.mem p.B (p.op + 8 * sW) = BitVec.ofNat 64 p.wp ∧
    word s.mem p.B (p.oq + 8 * sW) = BitVec.ofNat 64 p.wq ∧
    word s.mem p.B (p.op + 8 * sArr ja) = off p.B (p.op + slot p.wp ja) ∧
    word s.mem p.B (p.oq + 8 * sArr aN) = off p.B (p.oq + slot p.wq aN) ∧ ja < 8 ∧
    slot p.w 8 ≤ p.op ∧ p.op + slot p.wp 8 ≤ p.oq ∧ p.oq + slot p.wq 8 ≤ p.Z

theorem rowsHdr_split (ja : Nat) : rowsHdr ja = ([ldh .x5 Crt.sWsP] : List Instr) ++
    (([ldw .x11 .x5 (sArr ja), ldw .x13 .x5 sW, ldh .x5 Crt.sWsQ] : List Instr) ++
    ([ldw .x9 .x5 (sArr aN), ldw .x12 .x5 sW, ldh .x8 (sArr aAcc), movi .x7 0] : List Instr)) := rfl

/-- The header words the parts of `rowsHdr` read. -/
theorem RowsPre.hl {ja : Nat} {p : RowsPub} {s : State} (h : RowsPre ja p s) :
    (∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8) ∧
      (∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (p.op + 8 * i)) 8) ∧
      ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (p.oq + 8 * i)) 8 := by
  obtain ⟨hs, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩ := h
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have h8p := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  exact ⟨fun i hi => hs.ld (by omega), fun i hi => hs.ld (by omega), fun i hi => hs.ld (by omega)⟩

theorem RowsPre.keep {ja : Nat} {p : RowsPub} {s t : State} (h : RowsPre ja p s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : RowsPre ja p t := by
  obtain ⟨hs, h0, a, b, c, d, e, f, g, rest⟩ := h
  exact ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hm ▸ a, hm ▸ b, hm ▸ c, hm ▸ d, hm ▸ e, hm ▸ f, hm ▸ g, rest⟩

/-- `rowsHdr ja` and `mulRows`, given that the taint analysis checks the
part of `rowsHdr` that reads `p`'s workspace (`by taint_decide` for a given
`ja`). -/
theorem rows_ct {ja : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0, .x5]) (.block ([ldw .x11 .x5 (sArr ja), ldw .x13 .x5 sW,
      ldh .x5 Crt.sWsQ] : List Instr)) hc).isSome = true) :
    RelCT isa (Two (RowsPre ja)) (.seq (.block (rowsHdr ja)) mulRows) fun _ _ => True := by
  rw [rowsHdr_split]
  refine RelCT.seq (R := Two fun (p : RowsPub) t => t.gpr .x11 = off p.B (p.op + slot p.wp ja) ∧
      t.gpr .x13 = BitVec.ofNat 64 p.wp ∧ t.gpr .x9 = off p.B (p.oq + slot p.wq aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 p.wq ∧ t.gpr .x8 = off p.B (slot p.w aAcc))
    (RelCT.block_append (RelCT.seq (R := Two fun (p : RowsPub) t => RowsPre ja p t ∧
      t.gpr .x5 = off p.B p.op) ?_ (RelCT.block_append (RelCT.seq (R := Two fun (p : RowsPub) t =>
      RowsPre ja p t ∧ t.gpr .x5 = off p.B p.oq ∧ t.gpr .x11 = off p.B (p.op + slot p.wp ja) ∧
      t.gpr .x13 = BitVec.ofNat 64 p.wp) ?_ ?_)))) ?_
  · refine two_piece [.x0] (pins_of (fun p _ => p.B) fun p s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1) (by taint_decide) fun p s h => ?_
    obtain ⟨hl, -, -⟩ := h.hl
    obtain ⟨-, h0, -, hp, -⟩ := id h
    exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = off p.B p.op ∧ t.mem = s.mem)
      (by brun [h0, hdr_enc (show Crt.sWsP < 32 by decide), hl Crt.sWsP (by decide), hp])
      (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h5, hm⟩, k⟩ => ⟨h.keep hm k (by decide), h5⟩
  · refine two_piece [.x0, .x5] (pins_of (fun p r => if r = .x0 then p.B else off p.B p.op)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1
        · exact h.2) hT fun p s h => ?_
    obtain ⟨h, h5⟩ := h
    obtain ⟨hl, hlp, -⟩ := h.hl
    obtain ⟨-, h0, -, -, hq, hpw, -, hpa, -, hja, -⟩ := id h
    exact WP.mono (WP.keep [.x5, .x11, .x13] (Q := fun t => t.gpr .x5 = off p.B p.oq ∧
        t.gpr .x11 = off p.B (p.op + slot p.wp ja) ∧ t.gpr .x13 = BitVec.ofNat 64 p.wp ∧ t.mem = s.mem)
      (by brun [ldw, h0, h5, hdr_enc (show Crt.sWsQ < 32 by decide), hdr_enc (sArr_lt hja),
        hdr_enc (show sW < 32 by decide), hl Crt.sWsQ (by decide), hlp (sArr ja) (sArr_lt hja),
        hlp sW (by decide), hq, hpw, hpa]) rfl rfl rfl)
      fun t ⟨⟨h5', h11, h13, hm⟩, k⟩ => ⟨h.keep hm k (by decide), h5', h11, h13⟩
  · refine two_piece (Ψ := fun (p : RowsPub) t => t.gpr .x11 = off p.B (p.op + slot p.wp ja) ∧
        t.gpr .x13 = BitVec.ofNat 64 p.wp ∧ t.gpr .x9 = off p.B (p.oq + slot p.wq aN) ∧
        t.gpr .x12 = BitVec.ofNat 64 p.wq ∧ t.gpr .x8 = off p.B (slot p.w aAcc)) [.x0, .x5]
      (pins_of (fun p r => if r = .x0 then p.B else off p.B p.oq) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1
        · exact h.2.1) (by taint_decide) fun p s h => ?_
    obtain ⟨h, h5, h11, h13⟩ := h
    obtain ⟨hl, -, hlq⟩ := h.hl
    obtain ⟨-, h0, hacc, -, -, -, hqw, -, hqa, -⟩ := h
    exact WP.mono (WP.keep [.x7, .x8, .x9, .x12] (Q := fun t => t.gpr .x9 = off p.B (p.oq + slot p.wq aN) ∧
        t.gpr .x12 = BitVec.ofNat 64 p.wq ∧ t.gpr .x8 = off p.B (slot p.w aAcc))
      (by brun [ldw, h0, h5, hdr_enc (sArr_lt (show aAcc < 8 by decide)), hdr_enc (sArr_lt (show aN < 8 by decide)),
        hdr_enc (show sW < 32 by decide), hl (sArr aAcc) (by decide), hlq (sArr aN) (by decide),
        hlq sW (by decide), hqa, hqw, hacc]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h9, h12, h8⟩, k⟩ => ⟨(k.gpr .x11 (by decide)).trans h11, (k.gpr .x13 (by decide)).trans h13, h9,
        h12, h8⟩
  exact two_taint [.x11, .x13, .x9, .x12, .x8] (pins_of (fun p r => if r = .x11 then off p.B (p.op + slot p.wp ja)
      else if r = .x13 then BitVec.ofNat 64 p.wp else if r = .x9 then off p.B (p.oq + slot p.wq aN)
      else if r = .x12 then BitVec.ofNat 64 p.wq else off p.B (slot p.w aAcc)) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2) (by taint_decide)

end VG.Proof.Bignum.AArch64
