import VerifiedGarbage.Proof.Bignum.AArch64.CTR2

/-!
# `vg_rsa_public_precompute` on AArch64: constant time but for `n`

Every piece's addresses and branches depend only on the pointers, the
lengths and `n`: the load of `m` and `-m⁻¹` (`pcLoad_ct`), `R² mod m`
(`pcR2_ct`), the copies to `pre` (`pcOut_ct`), and the whole function
(`pcCode_constantTime`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem arr_fixed (w : Nat) {j : Nat} : 8 * 22 ≤ slot w j ∨ (8 * 6 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ 8 * 16) :=
  Or.inl (by unfold slot hdrBytes; omega)

theorem slot0_ge (w : Nat) : 8 * 31 + 8 ≤ slot w 0 ∧ slot w 0 + 8 * (w + 2) ≤ slot w 8 :=
  ⟨hdr_lt_slot w 0 (by decide), slot_le (by decide)⟩

/-! ## `main` -/

/-- The public data of `main`: the working space, `k`, `pre`, and `m` (its
bytes `nb` at `np`). -/
structure PcPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  nb : List Byte

abbrev PcPub.w (p : PcPub) : Nat := (p.k + 7) / 8
abbrev PcPub.N (p : PcPub) : Nat := Spec.Rsa.os2ip p.nb

/-- `pcMain_ok`'s hypotheses. -/
def PcM (p : PcPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word s.mem p.B (8 * sOut) = p.op ∧ word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.B (8 * sN) = p.np ∧ Src s p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ (∀ i < 2 * p.w, InRegions s.wr (off p.op (8 * i)) 8) ∧
    (∀ i < 16 * p.w, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i))

/-- `PcM` after code that changes only memory in the working space outside
the header's arguments, and not `x0`. -/
theorem PcM.congr {p : PcPub} {s t : State} (h : PcM p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcM p t := by
  obtain ⟨hs, h0, hZ, hk1, hk2, hO, hK, hN, hn, hnl, hv, hpw, hps⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hZ, hk1, hk2, (hfx sOut (by decide)).trans hO,
    (hfx sK (by decide)).trans hK, (hfx sN (by decide)).trans hN, hn.congrK hi k, hnl, hv,
    fun i hi => by rw [k.wr]; exact hpw i hi, hps⟩

theorem pins_PcM : Pins PcM [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- What the load of `m` and `-m⁻¹` needs: `PcM` but for `pre`. -/
def PcL (p : PcPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ word s.mem p.B (8 * sN) = p.np ∧ Src s p.B p.Z p.np p.nb ∧
    p.nb.length = p.k ∧ Spec.Rsa.modulusValid p.N p.k = true

theorem PcM.load {p : PcPub} {s : State} (h : PcM p s) : PcL p s :=
  let ⟨hs, h0, hZ, hk1, hk2, _, hK, hN, hn, hnl, hv, _⟩ := h
  ⟨hs, h0, hZ, hk1, hk2, hK, hN, hn, hnl, hv⟩

/-- `PcL` after code that changes only memory in the working space outside
the header's arguments, and not `x0`. -/
theorem PcL.congr {p : PcPub} {s t : State} (h : PcL p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcL p t := by
  obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, hn, hnl, hv⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hZ, hk1, hk2, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, hn.congrK hi k, hnl, hv⟩

theorem pins_PcL : Pins PcL [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the first block. -/
def Pc1 (p : PcPub) (s : State) : Prop :=
  PcL p s ∧ s.gpr .x1 = p.np ∧ s.gpr .x2 = BitVec.ofNat 64 p.k ∧ s.gpr .x8 = off p.B (slot p.w aN)

/-- After `-m⁻¹`: `R² mod m`'s hypotheses, and `PcM`. -/
def Pc3 (p : PcPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, PcM p s ∧ R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s

theorem pins_Pc1 : Pins Pc1 [.x0, .x1, .x2, .x8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.1.2.1, h₂.1.2.1]
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

/-- The load of `m` and `-m⁻¹` leak the same in runs that agree on `m`. -/
theorem pcLoad_ct : RelCT isa (Two PcL) (seqs pcLoad) fun _ _ => True := by
  unfold pcLoad
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := Pc1) _ pins_PcL (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (pcHead_ok hs h0 hZ (by omega) hK hN) fun t ⟨h1, h2, h8, _, _, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), h1, h2, h8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun (p : PcPub) s => s.gpr .x0 = p.B ∧ s.gpr .x8 = off p.B (slot p.w aN)) _
    pins_Pc1 (by taint_decide) ?_) ?_
  · intro p s ⟨h, h1, h2, h8⟩
    obtain ⟨hs, h0, hZ, hk1, hk2, -, -, hn, hnl, -⟩ := h
    exact WP.mono (loadArr_ok hs (by decide) hZ hn hnl (by omega) (by omega) h1 h2 h8) fun t ⟨_, _, k⟩ =>
      ⟨(k.gpr .x0 (by decide)).trans h0, (k.gpr .x8 (by decide)).trans h8⟩
  -- `-m⁻¹`.
  exact two_taint [.x0, .x8] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]) (by taint_decide)

/-- `R² mod m`'s hypotheses after the load of `m` and `-m⁻¹`. -/
theorem pcLoad_r2 {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hnl : nb.length = k) (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs pcLoad) s fun t => ∃ minv, R2Pre ⟨⟨B, Z, (k + 7) / 8, minv⟩, Spec.Rsa.os2ip nb⟩ t ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
  exact WP.mono (pcLoad_ok hs h0 hZ (by omega) (by omega) hK hN hnb hnl hodd)
    fun t ⟨minv, hg, hn, hinv, f, k⟩ => ⟨minv, ⟨⟨hg, hZ⟩, by dsimp only; omega, by dsimp only; omega, hn, hinv,
      hodd, hlo⟩, f, k⟩

/-! ## `R² mod m` -/

/-- `main`'s public data with `-m⁻¹`. -/
abbrev PcPub.L (q : PcPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, q.1.w, q.2⟩

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem pc3_minv {p : PcPub} {s₁ s₂ : State} {mi₁ mi₂ : BitVec 64}
    (h₁ : R2Pre ⟨⟨p.B, p.Z, p.w, mi₁⟩, p.N⟩ s₁) (h₂ : R2Pre ⟨⟨p.B, p.Z, p.w, mi₂⟩, p.N⟩ s₂) : mi₁ = mi₂ := by
  have e : ∀ {s : State} {mi : BitVec 64}, R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s →
      ((p.N % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 := fun h => by
    have hw := h.2.1
    have hv := h.2.2.2.1
    have hi := h.2.2.2.2.1
    dsimp only at hw hv hi
    rwa [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega), hv] at hi
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.2.2.2.2.2.1) (e h₁) (e h₂)

/-- What the copies to `pre` need. -/
def PcO (q : PcPub × BitVec 64) (s : State) : Prop :=
  GoodL (PcPub.L q) s ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧ word s.mem q.1.B (8 * sOut) = q.1.op ∧
    (∀ i < 2 * q.1.w, InRegions s.wr (off q.1.op (8 * i)) 8) ∧
    (∀ i < 16 * q.1.w, q.1.Z ≤ ofs q.1.B (q.1.op + BitVec.ofNat 64 i))

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem pcR2_ct (M : Mont) : RelCT isa (Two Pc3) (seqs (r2Steps M.mm)) (Two PcO) := by
  have h := two_post (Φ := fun (q : PcPub × BitVec 64) s => PcM q.1 s ∧ R2Pre ⟨PcPub.L q, q.1.N⟩ s)
    (Ψ := PcO) (two_map (fun q => (⟨PcPub.L q, q.1.N⟩ : R2Pub)) (fun _ _ h => h.2) (r2_ct M)) ?_
  · exact h.mono (fun _ _ hp => two_bind (fun p s₁ s₂ ⟨mi₁, m₁, r₁⟩ ⟨mi₂, m₂, r₂⟩ => by
      obtain rfl := pc3_minv r₁ r₂
      exact ⟨(p, mi₁), ⟨m₁, r₁⟩, m₂, r₂⟩) hp) fun _ _ h => h
  rintro ⟨p, mi⟩ s ⟨hm, hr⟩
  obtain ⟨hg, hw, hw', hn, hinv, hodd, hlo⟩ := hr
  dsimp only at hg hw hw' hn hinv hodd hlo
  refine WP.mono (r2_ok M hg.1 hg.2 hw hw' hn hinv hodd hlo) fun t ⟨hg', _, _, f, k⟩ =>
    ⟨⟨hg', hg.2⟩, hw, hw', ?_, fun i hi => by rw [k.wr]; exact hm.2.2.2.2.2.2.2.2.2.2.2.1 i hi,
      hm.2.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [(Fixed.of_frm f (r2Ranges_fixed _)) sOut (by decide)]
  exact hm.2.2.2.2.2.1

/-! ## The copies to `pre` -/

/-- `Good` after code that changes only memory outside the working space. -/
theorem Good.of_inScr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hi : ∀ x, ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = B) : Good t B Z w minv := by
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := w) (show 0 < 8 by decide)
  have hw : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    Mem.readW_congr fun b hb => hi _ (by rw [ofs_off B (d := 8 * i) (i := b) (by omega)]; omega)
  exact ⟨hg.scr.congr hwr, h0, ⟨by rw [hw sW (by decide)]; exact hg.hdr.hw,
    by rw [hw sMinv (by decide)]; exact hg.hdr.hminv,
    fun j hj => by rw [hw (sArr j) (by unfold sArr; omega)]; exact hg.hdr.harr j hj⟩⟩

/-- Before the first copy. -/
def PcO1 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x16 = off q.1.B (slot q.1.w aN) ∧
    s.gpr .x17 = off q.1.op 0

/-- After the first copy. -/
def PcO2 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x17 = off q.1.op (8 * q.1.w)

/-- Before the second copy. -/
def PcO3 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x16 = off q.1.B (slot q.1.w aR2) ∧
    s.gpr .x17 = off q.1.op (8 * q.1.w)

theorem pins_PcO : Pins PcO [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.x0, h₂.1.1.x0]

/-- A copy of `w` words from the working space to `pre` at `pre + 8 d`,
`d ≤ w`: the working space is as it was. -/
theorem pcCopy_ok {q : PcPub × BitVec 64} {s : State} (h : PcO q s) {e d : Nat} (hd : d ≤ q.1.w)
    (he : e + 8 * q.1.w ≤ q.1.Z) (h16 : s.gpr .x16 = off q.1.B e) (h17 : s.gpr .x17 = off q.1.op (8 * d))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 q.1.w) :
    WP isa copyWords s fun t => PcO q t ∧ t.gpr .x17 = off q.1.op (8 * d + 8 * q.1.w) ∧
      Keep [.x3, .x14, .x16, .x17] s t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  have hs : Scr s q.1.B q.1.Z := hg.1.scr
  have hn := hs.nowrap
  have hZ : slot q.1.w 8 ≤ q.1.Z := hg.2
  have hsep : ∀ x, ofs q.1.B x < q.1.Z → 16 * q.1.w ≤ ofs q.1.op x := fun x hx => le_ofs_of_sep hps hx
  refine WP.mono (copyWords_ok h16 h17 h12 (by omega) (by omega) (by omega)
    (fun j hj => hs.ld (by omega))
    (fun j hj => by rw [show 8 * d + 8 * j = 8 * (d + j) by omega]; exact hpw (d + j) (by omega))
    (fun j hj b hb => Or.inr (Nat.le_trans (by omega)
      (hsep _ (by rw [ofs_off q.1.B (d := e + 8 * j) (i := b) (by omega)]; omega)))))
    fun t ⟨_, _, ho, _, h17', k⟩ => ?_
  have hi : ∀ x, ofs q.1.B x < q.1.Z → t.mem x = s.mem x := fun x hx =>
    ho x (Or.inr (by have := hsep x hx; omega))
  refine ⟨⟨⟨Good.of_inScr (hg.1 : Good s q.1.B q.1.Z q.1.w q.2) hZ hi k.wr
    ((k.gpr .x0 (by decide)).trans hg.1.x0), hZ⟩, hw, hw', ?_,
    fun i hi' => by rw [k.wr]; exact hpw i hi', hps⟩, h17', k⟩
  rw [← hO]
  exact Mem.readW_congr fun b hb => hi _ (by
    have := hdr_lt_slot q.1.w 0 (show 31 < 32 by decide)
    have := slot_le (w := q.1.w) (show 0 < 8 by decide)
    rw [ofs_off q.1.B (d := 8 * sOut) (i := b) (by unfold sOut sFn; omega)]; unfold sOut sFn; omega)

theorem PcO.mem {q : PcPub × BitVec 64} {s t : State} (h : PcO q s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcO q t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  exact ⟨⟨Good.of_inScr (hg.1 : Good s q.1.B q.1.Z q.1.w q.2) hg.2 (fun x _ => by rw [hm]) k.wr
    ((k.gpr .x0 hr).trans hg.1.x0), hg.2⟩, hw, hw', by rw [hm]; exact hO,
    fun i hi => by rw [k.wr]; exact hpw i hi, hps⟩

/-- The copies to `pre` leak the same in runs with the same working space and
`pre`. -/
theorem pcOut_ct : RelCT isa (Two PcO) (seqs Precompute.pcOut) fun _ _ => True := by
  unfold Precompute.pcOut
  -- The first copy's registers.
  refine RelCT.seq (two_piece (Ψ := PcO1) _ pins_PcO (by taint_decide) ?_) ?_
  · intro q s h
    have hs : Scr s q.1.B q.1.Z := h.1.1.scr
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := slot0_ge q.1.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.1.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 q.1.w ∧
        t.gpr .x16 = off q.1.B (slot q.1.w aN) ∧ t.gpr .x17 = off q.1.op 0 ∧ t.mem = s.mem) (by
      brun [h.1.1.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
        hdr_enc (show sOut < 32 by decide), hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
        h.1.1.hdr.hw, h.1.1.hdr.harr aN (by decide), h.2.2.2.1]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h12, h16, h17, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h12, h16, h17⟩
  -- The first copy.
  refine RelCT.seq (two_piece (Ψ := PcO2) [.x16, .x17, .x12] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, h16, h17⟩
    have := slot_le (w := q.1.w) (show aN < 8 by decide)
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    exact WP.mono (pcCopy_ok h (d := 0) (by omega) (by omega) h16 (by rw [h17]) h12)
      fun t ⟨h', h17', k⟩ => ⟨h', (k.gpr .x12 (by decide)).trans h12, by rw [h17']; congr 1; omega⟩
  -- The second copy's registers.
  refine RelCT.seq (two_piece (Ψ := PcO3) _ (fun q s₁ s₂ h₁ h₂ => pins_PcO q s₁ s₂ h₁.1 h₂.1)
    (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, h17⟩
    have hs : Scr s q.1.B q.1.Z := h.1.1.scr
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := slot0_ge q.1.w
    refine WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off q.1.B (slot q.1.w aR2) ∧ t.mem = s.mem) (by
      brun [h.1.1.x0, hdr_enc (show sArr aR2 < 32 by decide), hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
        h.1.1.hdr.harr aR2 (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h16, hm⟩, k⟩ => ⟨h.mem hm k (by decide), (k.gpr .x12 (by decide)).trans h12, h16,
        (k.gpr .x17 (by decide)).trans h17⟩
  -- The second copy and the return.
  exact two_taint [.x16, .x17, .x12, .x0] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.1.1.1.x0, h₂.1.1.1.x0]) (by taint_decide)

/-- `main` leaks the same in runs that agree on the public data and `n`. -/
theorem pcMain_ct (M : Mont) : RelCT isa (Two PcM) (Precompute.main M.mm) fun _ _ => True := by
  rw [pcMain_eq M]
  refine RelCT.seqs_append (by simp [pcLoad]) (by simp [r2Steps]) (RelCT.seq (R := Two Pc3)
    (two_post (pcLoad_ct.mono (fun _ _ h => two_mono (fun _ _ h => PcM.load h) h) fun _ _ _ => trivial)
      fun p s h => ?_) ?_)
  · have h' := h
    obtain ⟨hs, h0, hZ, hk1, hk2, -, hK, hN, hn, hnl, hv, -⟩ := h'
    refine WP.mono (pcLoad_r2 hs h0 hZ hk1 hk2 hK hN hn hnl hv) fun t ⟨mi, hr, f, k⟩ =>
      ⟨mi, h.congr f (fun r hr => Nat.le_trans (pcLoadRanges_le _ r hr) hZ) (pcLoadRanges_fixed _) k (by decide), hr⟩
  exact RelCT.seqs_append (by simp [r2Steps]) (by simp [Precompute.pcOut]) (RelCT.seq (pcR2_ct M) pcOut_ct)

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def PcC (p : PcPub) (s : State) : Prop :=
  pcContract.pre s ∧ s.gpr .x4 = p.B ∧ (s.gpr .x5).toNat * 8 = p.Z ∧ (s.gpr .x3).toNat = p.k ∧
    s.gpr .x0 = p.op ∧ s.gpr .x2 = p.np ∧ Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = p.nb

/-- After the entry and the modulus' check. -/
def PcC3 (p : PcPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ t.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word t.mem p.B (8 * sOut) = p.op ∧ word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word t.mem p.B (8 * sN) = p.np ∧ Src t p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    (∀ i < 2 * p.w, InRegions t.wr (off p.op (8 * i)) 8) ∧
    (∀ i < 16 * p.w, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i)) ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid p.N p.k).toNat

/-- `vg_rsa_public_precompute` leaks the same in runs that agree on the public
data and `n`. -/
theorem pcCode_ct (M : Mont) : RelCT isa (Two PcC) (Precompute.code M.mm) fun _ _ => True := by
  unfold Precompute.code
  refine RelCT.seq (two_piece (Ψ := PcC3) [.x4, .x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨-, a₁, -, c₁, -, d₁, -⟩ := h₁
    obtain ⟨-, a₂, -, c₂, -, d₂, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [d₁, d₂]
    · rw [← ofNat_toNat64 (s₁.gpr .x3), ← ofNat_toNat64 (s₂.gpr .x3), c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro ⟨B, Z, k, op, np, nb⟩ s ⟨hs, hB, hZ, hk, hop, hnp, hnb⟩
    have c := pcCtx_of hs
    have hZ' := c.hZ
    have hk1 := c.hk1
    have hk2 := c.hk2
    have hn := c.hs.nowrap
    rw [WP.block_append_iff]
    refine WP.mono (pcEntry_ok rfl fun i hi => c.hs.st (by omega)) fun t₁ ⟨h0, hO, hN, hK, ho₁, k₁⟩ => ?_
    have i₁ : InScr (s.gpr .x4) ((s.gpr .x5).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
    have hnb₁ := c.hnb.congrK i₁ k₁
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (k₁.gpr .x2 (by decide))
      (by rw [k₁.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2
      (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
      (fun i hi => hnb₁.val i _)) (by decide) (by decide) (by decide +kernel))
      fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
    have kk := k₁.trans k₂
    subst hB hZ hk hop hnp hnb
    exact ⟨c.hs.congr kk.wr, (k₂.gpr .x0 (by decide)).trans h0,
      show slot (((s.gpr .x3).toNat + 7) / 8) 8 ≤ (s.gpr .x5).toNat * 8 by unfold slot hdrBytes; omega, hk1, hk2,
      by rw [hm₂]; exact hO, by rw [hm₂, hK, ofNat_toNat64], by rw [hm₂]; exact hN,
      c.hnb.congrK (by rw [hm₂]; exact i₁) kk, bytesAt_length _ _ _,
      fun i hi => by rw [kk.wr]; exact c.hpw i hi, c.hps, hz₂⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by
    rw [eval_zero, eval_zero, h₁.2.2.2.2.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2.2.2.2.2]) ?_ ?_
  · -- `fail`.
    unfold Precompute.fail
    refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .x1 = off p.op 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 (2 * p.w)) [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.1, h₂.1.2.1]) (by taint_decide) ?_)
      (two_taint [.x1, .x2] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    rintro p t ⟨⟨hs, h0, hZ, hk1, hk2, hO, hK, -⟩, -⟩
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = off p.op 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 (2 * p.w)) (by
      brun [h0, hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide), hl sOut (by decide),
        hl sK (by decide), hO, hK, two_w p.k (by omega)]) (by decide) (by decide) (by decide +kernel))
      fun t' ⟨h, _⟩ => h
  · -- `main`.
    refine two_map id (fun p t ⟨⟨hs, h0, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, hpw, hps, hz⟩, he⟩ =>
      ⟨hs, h0, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, ?_, hpw, hps⟩) (pcMain_ct M)
    rw [eval_zero, hz] at he
    cases hv : Spec.Rsa.modulusValid p.N p.k
    · rw [hv] at he; simp at he
    · exact hv

/-- The public data of a state. -/
def pcPubOf (s : State) : PcPub :=
  ⟨s.gpr .x4, (s.gpr .x5).toNat * 8, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩

/-- `vg_rsa_public_precompute` is constant time but for `n`. -/
theorem pcCode_constantTime (M : Mont) :
    ConstantTime isa pcContract.pre pcContract.pub (Precompute.code M.mm) := by
  refine RelCT.constantTime ((pcCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pcPubOf s₁, ?_, ?_, hp.1⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨-, hl, h0, -, h2, h3, h4, h5⟩ := hp
    have hn := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    exact ⟨h₂, h4.symm, congrArg (fun x : BitVec 64 => x.toNat * 8) h5.symm, congrArg BitVec.toNat h3.symm,
      h0.symm, h2.symm, hn.symm⟩

end VG.Proof.Bignum.AArch64
