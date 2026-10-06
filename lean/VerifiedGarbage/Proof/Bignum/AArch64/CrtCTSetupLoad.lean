import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-!
# RSA with the CRT on AArch64: constant time of the loads into the primes'
workspaces

`loadArr j sp sl` clears an array of a prime's workspace (`zeroArr_ct`),
reads the bytes' pointer and length through the workspace's link, and loads
them (`loadArr_ct`): the link is pinned by correctness, the rest by the taint
analysis.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A prime's workspace context with the same memory, `x0` kept. -/
theorem SubCtx.mem {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx s B Z o w wx minv)
    (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : SubCtx t B Z o w wx minv :=
  ⟨h.scr.congr k.wr, (k.gpr .x0 hr).trans h.x0, hm ▸ h.hdr, hm ▸ h.link, hm ▸ h.nw, hm ▸ h.narr, h.lo, h.hi⟩

theorem LPre.mem {j sp sl : Nat} {p : BPub} {s t : State} (h : LPre j sp sl p s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : LPre j sp sl p t := by
  obtain ⟨minv, bs, hc, a1, a2, a3, a4, a5, a6, hp, hl, hbl, hsrc, b1, b2, b3⟩ := h
  exact ⟨minv, bs, hc.mem hm k hr, a1, a2, a3, a4, a5, a6, hm ▸ hp, hm ▸ hl, hbl,
    hsrc.congrK (by rw [hm]; exact InScr.refl _ _ _) k, b1, b2, b3⟩

/-- `zeroArr j` keeps `LPre`. -/
theorem LPre.zero {j sp sl : Nat} {p : BPub} {s : State} (h : LPre j sp sl p s) :
    WP isa (zeroArr j) s (LPre j sp sl p) := by
  obtain ⟨minv, bs, hc, hw2, hwx, hw30, hj, hsp, hsl, hp, hl, hbl, hsrc, hk1, hk', hkw⟩ := h
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hlo := hc.lo
  have h8 := hdr_lt_slot p.x.w 8 (show 31 < 32 by decide)
  have h256 : 256 ≤ slot p.x.wx 8 := by unfold slot hdrBytes; omega
  have hJ := slot_le (w := p.x.wx) hj
  have hJ0 := hdr_lt_slot p.x.wx j (show 31 < 32 by decide)
  have ho64 : p.x.o < 2 ^ 64 := by omega
  have hr : ∀ r ∈ [(slot p.x.wx j, 8 * (p.x.wx + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.x.wx 8 := by
    simp only [List.mem_singleton, forall_eq]; omega
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega) hj) fun t ⟨_, ho₁, k₁⟩ => ?_
  have f₁ : Frm (off p.x.B p.x.o) [(slot p.x.wx j, 8 * (p.x.wx + 2))] s.mem t.mem := Frm.of_outside ho₁ (by simp)
  have hb : ∀ i < 32, word t.mem p.x.B (8 * i) = word s.mem p.x.B (8 * i) := fun i hi' =>
    f₁.word_below (fun r hr' => (hr r hr').2) (by omega) ho64 (by omega)
  refine ⟨minv, bs, hc.of_frm f₁ hr k₁.wr (k₁.gpr .x0 (by decide)), hw2, hwx, hw30, hj, hsp, hsl,
    (hb sp hsp).trans hp, (hb sl hsl).trans hl, hbl, hsrc.congrK ?_ k₁, hk1, hk', hkw⟩
  exact InScr.of_frm (f₁.rebase ho64 fun r hr' => by have := (hr r hr').2; omega) fun r hr' => by
    simp only [shiftRanges, List.map_cons, List.map_nil, List.mem_singleton] at hr'
    subst hr'; simp only; omega

theorem pins_lpre {j sp sl : Nat} : Pins (LPre j sp sl) [.x0] :=
  pins_of (fun p _ => off p.x.B p.x.o) fun _ _ ⟨_, _, hc, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.x0

/-- The registers of `loadBE`. -/
def LRegs (j : Nat) (p : BPub) (t : State) : Prop :=
  t.gpr .x1 = p.ptr ∧ t.gpr .x2 = BitVec.ofNat 64 p.len ∧ t.gpr .x8 = off p.x.B (p.x.o + slot p.x.wx j)

/-- `loadArr j sp sl`, given that the taint analysis checks its header loads. -/
theorem loadArr_ct {j sp sl : Nat} (hj : j < 8) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hZ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr j), ldh .x12 sW, movi .x7 0])
      hc₁).isSome = true)
    (hT : (taint.check (Taint.ofRegs [.x0, .x5]) (.block [ldw .x1 .x5 sp, ldw .x2 .x5 sl, ldh .x8 (sArr j)])
      hc₂).isSome = true) :
    LoadCT j sp sl := by
  unfold LoadCT loadArr
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : BPub => (⟨off p.x.B p.x.o, slot p.x.wx 8, p.x.wx⟩ : Ws))
    (fun p s ⟨minv, _, hc, _⟩ => ⟨minv, hc.good, Nat.le_refl _⟩) (zeroArr_ct hj hZ)) fun p s h => h.zero) ?_
  refine RelCT.seq (RelCT.block_append (l₁ := ([ldh .x5 sLink] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun p t => LPre j sp sl p t ∧ t.gpr .x5 = p.x.B) [.x0]
      (fun p s₁ s₂ h₁ h₂ => pins_lpre p s₁ s₂ h₁ h₂) (by taint_decide) ?_)
    (two_piece (Ψ := LRegs j) [.x0, .x5]
      (pins_of (fun (p : BPub) r => if r = .x0 then off p.x.B p.x.o else p.x.B) fun p s ⟨⟨_, _, hc, _⟩, h5⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hc.x0
        · exact h5) hT ?_)))
    (two_taint [.x1, .x2, .x8] (pins_of (fun (p : BPub) r => if r = .x1 then p.ptr else if r = .x2 then
        BitVec.ofNat 64 p.len else off p.x.B (p.x.o + slot p.x.wx j)) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2) (by taint_decide))
  · intro p s h
    have h' := h
    obtain ⟨_, _, hc, -⟩ := h'
    exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.x.B ∧ t.mem = s.mem)
      (by brun [hc.x0, hdr_enc (show sLink < 32 by decide), hc.ld' (show sLink < 32 by decide), hc.link'])
      (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h5, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h5⟩
  · rintro p s ⟨⟨_, bs, hc, -, -, -, hj, hsp, hsl, hp, hl, hbl, -⟩, h5⟩
    unfold LRegs; rw [← hbl]
    exact WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = p.ptr ∧
        t.gpr .x2 = BitVec.ofNat 64 bs.length ∧ t.gpr .x8 = off p.x.B (p.x.o + slot p.x.wx j))
      (by brun [ldw, hc.x0, h5, hdr_enc hsp, hdr_enc hsl, hdr_enc (sArr_lt hj), hc.ldn hsp, hp, hc.ldn hsl, hl,
        hc.ld' (sArr_lt hj), hc.harr' hj]) rfl rfl rfl) fun t h => h.1

theorem loadArr_ct_pN : LoadCT Public.aN sP sPlen := loadArr_ct (by decide) (by taint_decide) (by taint_decide)

theorem loadArr_ct_pI : LoadCT aChunk sQinv sPlen := loadArr_ct (by decide) (by taint_decide) (by taint_decide)

theorem loadArr_ct_qN : LoadCT Public.aN sQ sQlen := loadArr_ct (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.AArch64
