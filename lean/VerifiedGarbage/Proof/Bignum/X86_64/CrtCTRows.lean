import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs

/-!
# RSA with the CRT on x86-64: products in constant time

`zeroAccs` (`zeroAccs_ct`), and a product of an array of `p`'s workspace and
`q`'s `n` into the modulus' accumulators (`rows_ct`), which `pqProduct` and
`finish` make. `rowsHdr` loads each prime's workspace's base from the header
and then its header through it: the taint analysis, to which memory is
secret, checks it in three parts, each from the registers that correctness
pins after the one before.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- `acc := 0` over `2 w + 2` words. -/
theorem zeroAccs_ct : RelCT isa (Two GoodW) (seqs Crt.zeroAccs) fun _ _ => True := by
  unfold Crt.zeroAccs
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .r8 = off L.B (slot L.w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 L.w) [.rdi] pins_goodW (by taint_decide) fun L s h => ?_)
    (two_taint [.r8, .rbx] (pins_of (fun L r => if r = .r8 then off L.B (slot L.w aAcc) else BitVec.ofNat 64 L.w)
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off L.B (slot L.w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 L.w)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aAcc) (by decide), hl sW (by decide),
      hg.hdr.harr aAcc (by decide), hg.hdr.hw]) rfl) fun _ h => h.1

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
  Scr s p.B p.Z ∧ s.gpr .rdi = p.B ∧ word s.mem p.B (8 * sArr aAcc) = off p.B (slot p.w aAcc) ∧
    word s.mem p.B (8 * Crt.sWsP) = off p.B p.op ∧ word s.mem p.B (8 * Crt.sWsQ) = off p.B p.oq ∧
    word s.mem (off p.B p.op) (8 * sW) = BitVec.ofNat 64 p.wp ∧
    word s.mem (off p.B p.oq) (8 * sW) = BitVec.ofNat 64 p.wq ∧
    word s.mem (off p.B p.op) (8 * sArr ja) = off p.B (p.op + slot p.wp ja) ∧
    word s.mem (off p.B p.oq) (8 * sArr aN) = off p.B (p.oq + slot p.wq aN) ∧ ja < 8 ∧
    slot p.w 8 ≤ p.op ∧ p.op + slot p.wp 8 ≤ p.oq ∧ p.oq + slot p.wq 8 ≤ p.Z

theorem rowsHdr_split (ja : Nat) : rowsHdr ja = ([.mov .rax (.mem (hdr Crt.sWsP))] : List Instr) ++
    (([.mov .r11 (.mem (Crt.ws .rax (sArr ja))), .mov .r10 (.mem (Crt.ws .rax sW)),
      .mov .rax (.mem (hdr Crt.sWsQ))] : List Instr) ++
    ([.mov .r9 (.mem (Crt.ws .rax (sArr aN))), .mov .r12 (.mem (Crt.ws .rax sW)),
      .mov .r8 (.mem (hdr (sArr aAcc)))] : List Instr)) := rfl

/-- The header words the parts of `rowsHdr` read. -/
theorem RowsPre.hl {ja : Nat} {p : RowsPub} {s : State} (h : RowsPre ja p s) :
    (∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8) ∧
      (∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.B p.op) (8 * i)) 8) ∧
      ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off p.B p.oq) (8 * i)) 8 := by
  obtain ⟨hs, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩ := h
  have hn := hs.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have h8p := hdr_lt_slot p.wp 8 (show 31 < 32 by decide)
  have h8q := hdr_lt_slot p.wq 8 (show 31 < 32 by decide)
  exact ⟨fun i hi => hs.ld (by omega),
    fun i hi => (hs.sub (o := p.op) (n := slot p.wp 8) (by omega) (by omega)).ld (by omega),
    fun i hi => (hs.sub (o := p.oq) (n := slot p.wq 8) (by omega) (by omega)).ld (by omega)⟩

theorem RowsPre.keep {ja : Nat} {p : RowsPub} {s t : State} (h : RowsPre ja p s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : RowsPre ja p t := by
  obtain ⟨hs, hdi, a, b, c, d, e, f, g, rest⟩ := h
  exact ⟨hs.congr k.2.2, (k.gpr hr).trans hdi, hm ▸ a, hm ▸ b, hm ▸ c, hm ▸ d, hm ▸ e, hm ▸ f, hm ▸ g, rest⟩

/-- `rowsHdr ja` and `mulRows`, given that the taint analysis checks the
part of `rowsHdr` that reads `p`'s workspace (`by taint_decide` for a given
`ja`). -/
theorem rows_ct {ja : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi, .rax]) (.block ([.mov .r11 (.mem (Crt.ws .rax (sArr ja))),
      .mov .r10 (.mem (Crt.ws .rax sW)), .mov .rax (.mem (hdr Crt.sWsQ))] : List Instr)) hc).isSome = true) :
    RelCT isa (Two (RowsPre ja)) (.seq (.block (rowsHdr ja)) Crt.mulRows) fun _ _ => True := by
  rw [rowsHdr_split]
  refine RelCT.seq (R := Two fun (p : RowsPub) t => t.gpr .r11 = off p.B (p.op + slot p.wp ja) ∧
      t.gpr .r10 = BitVec.ofNat 64 p.wp ∧ t.gpr .r9 = off p.B (p.oq + slot p.wq aN) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .r8 = off p.B (slot p.w aAcc)) (RelCT.block_append (RelCT.seq (R := Two fun (p : RowsPub) t => RowsPre ja p t ∧
      t.gpr .rax = off p.B p.op) ?_ (RelCT.block_append (RelCT.seq (R := Two fun (p : RowsPub) t => RowsPre ja p t ∧
      t.gpr .rax = off p.B p.oq ∧ t.gpr .r11 = off p.B (p.op + slot p.wp ja) ∧
      t.gpr .r10 = BitVec.ofNat 64 p.wp) ?_ ?_)))) ?_
  · refine two_piece [.rdi] (pins_of (fun p _ => p.B) fun p s h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.2.1) (by taint_decide) fun p s h => ?_
    obtain ⟨hl, -, -⟩ := h.hl
    obtain ⟨-, hdi, -, hp, -⟩ := id h
    exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = off p.B p.op ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hdi, hdrOff, hl Crt.sWsP (by decide), hp]) rfl)
      fun t ⟨⟨hax, hm⟩, k⟩ => ⟨h.keep hm k (by decide), hax⟩
  · refine two_piece [.rdi, .rax] (pins_of (fun p r => if r = .rdi then p.B else off p.B p.op)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1
        · exact h.2) hT fun p s h => ?_
    obtain ⟨h, hax⟩ := h
    obtain ⟨hl, hlp, -⟩ := h.hl
    obtain ⟨-, hdi, -, -, hq, hpw, -, hpa, -, hja, -⟩ := id h
    exact WP.mono (WP.keep [.r11, .r10, .rax] (Q := fun t => t.gpr .rax = off p.B p.oq ∧
        t.gpr .r11 = off p.B (p.op + slot p.wp ja) ∧ t.gpr .r10 = BitVec.ofNat 64 p.wp ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, Crt.ws, hdi, hax, hdrOff, hl Crt.sWsQ (by decide),
        hlp (sArr ja) (by unfold sArr; omega), hlp sW (by decide), hq, hpw, hpa]) rfl)
      fun t ⟨⟨hax', h11, h10, hm⟩, k⟩ => ⟨h.keep hm k (by decide), hax', h11, h10⟩
  · refine two_piece (Ψ := fun (p : RowsPub) t => t.gpr .r11 = off p.B (p.op + slot p.wp ja) ∧
        t.gpr .r10 = BitVec.ofNat 64 p.wp ∧ t.gpr .r9 = off p.B (p.oq + slot p.wq aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .r8 = off p.B (slot p.w aAcc)) [.rdi, .rax]
      (pins_of (fun p r => if r = .rdi then p.B else off p.B p.oq) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.2.1
        · exact h.2.1) (by taint_decide) fun p s h => ?_
    obtain ⟨h, hax, h11, h10⟩ := h
    obtain ⟨hl, -, hlq⟩ := h.hl
    obtain ⟨-, hdi, hacc, -, -, -, hqw, -, hqa, -⟩ := h
    exact WP.mono (WP.keep [.r9, .r12, .r8] (Q := fun t => t.gpr .r9 = off p.B (p.oq + slot p.wq aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.wq ∧ t.gpr .r8 = off p.B (slot p.w aAcc))
      (by xrun [State.ea, hdr, Crt.ws, hdi, hax, hdrOff, hl (sArr aAcc) (by decide),
        hlq (sArr aN) (by decide), hlq sW (by decide), hqa, hqw, hacc]) rfl)
      fun t ⟨⟨h9, h12, h8⟩, k⟩ => ⟨(k.gpr (by decide)).trans h11, (k.gpr (by decide)).trans h10, h9, h12, h8⟩
  exact two_taint [.r11, .r10, .r9, .r12, .r8] (pins_of (fun p r => if r = .r11 then off p.B (p.op + slot p.wp ja)
      else if r = .r10 then BitVec.ofNat 64 p.wp else if r = .r9 then off p.B (p.oq + slot p.wq aN)
      else if r = .r12 then BitVec.ofNat 64 p.wq else off p.B (slot p.w aAcc)) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2.1
        · exact h.2.2.2.2) (by taint_decide)

end VG.Proof.Bignum.X86_64
