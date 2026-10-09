import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Bulk

/-!
# ChaCha20 and Poly1305 together (x86-64): `open`'s whole chunks

`Stitch.chunkO` absorbs the 512 bytes at `rsi` while ChaCha20's rounds run
(`srounds_ok`, as `seal`'s chunks do), then XORs the keystream into the same
bytes and advances `rsi` past them (`chunkMainO_ok`). Before chunk `t`
(`LO`), the first `512 t` bytes are decrypted, the counter is advanced by
`8 t`, the first `512 t` bytes of ciphertext (as they were on entry) are
absorbed, and the bytes left are `L - 512 t`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds Consts Incs stR bufR slotsR dR5 DWin W2 plus hiR
  setup_ok finish_ok W2_frame incs_frame hiR_slots hiR_sub slotsR_sub plus_block ks_shift ctr_add)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock keystream)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The 512 bytes at `q` absorbed, then XORed with eight blocks of keystream
from the state at `st`, and `rsi` advanced past them. -/
theorem chunkMainO_ok {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hwd : DWin s.wr q)
    (hin : ∀ off n, off + n ≤ 512 → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsd : (stR st).Disjoint (dR5 q)) (dsb : (stR st).Disjoint (bufR buf))
    (dbd : (bufR buf).Disjoint (dR5 q)) (dqs : (dR5 q).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa chunkMainO s fun s' =>
        (∀ k < 512, s'.mem (q + BitVec.ofNat 64 k) = s.mem (q + BitVec.ofNat 64 k) ^^^
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (k / 64))).getD (k % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q 512)) s' ∧
        Frame [slotsR buf, dR5 q] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.gpr .rsi = q + 512 ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold chunkMainO
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  have q₁ : bytesAt s₁.mem q 512 = bytesAt s.mem q 512 := by
    have := bytes_frame F₁ dqs (j := 0) (n := 512) (by decide)
    simpa using this
  have h0 : SR buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      rw [show 16 * firstBlock 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl,
        VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (srounds_ok hk (by rw [g₁, hrcx]) (by rw [g₁, hrsi]) (by rw [wr₁]; exact hb) c₁.m8 dqs
    (by rw [rd₁, wr₁]; exact hin) 10 (by decide) h0) fun s₂ h₂ => ?_)
  have F₂ : Frame [slotsR buf] s.mem s₂.mem := F₁.trans h₂.frame
  have wr₂ : s₂.wr = s.wr := by rw [h₂.wr, wr₁]
  have gk₂ : ∀ r, r ∉ absorbRegs → s₂.gpr r = s.gpr r := fun r hr => by rw [h₂.gpr r hr, g₁]
  have inc₂ : Incs buf s₂.mem := incs_frame hc.inc F₂ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.block_append (WP.mono (finish_ok h₂.holds (st := st) (by rw [gk₂ _ (by decide), hrdi])
    (by rw [gk₂ _ (by decide), hrcx]) (by rw [gk₂ _ (by decide), hrsi]) (by rw [wr₂]; exact hst)
    (by rw [wr₂]; exact hb) (by rw [wr₂]; exact hwd) inc₂ dsd dsb dbd) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  refine WP.mono (addRsi_ok s₃) fun s₄ ⟨rsi₄, g₄, _, _, m₄, rd₄, wr₄⟩ => ?_
  have hS : stateAt s₂.mem st = stateAt s.mem st :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using dsb.sub_right (slotsR_sub buf))
  have hq₂ : ∀ k < 512, s₂.mem (q + BitVec.ofNat 64 k) = s.mem (q + BitVec.ofNat 64 k) := by
    intro k hk'
    refine F₂ _ ?_
    simp only [List.mem_singleton, forall_eq]
    intro hc'
    exact dqs.symm _ hc' (Offset.contains_base q (d := k) (n := 1) (k := 512) (by omega) (by lit_omega))
  have gk : ∀ r, r ∉ absorbRegs → r ≠ .rsi → s₄.gpr r = s.gpr r := fun r hr hs => by
    rw [g₄ r hs, g₃, gk₂ r hr]
  refine ⟨fun k hk' => by rw [m₄, d₃ k hk', hS, hq₂ k hk'], ?_, by rw [m₄]; exact (F₂.mono (by simp)).trans f₃,
    gk, by rw [rsi₄, g₃, gk₂ _ (by decide), hrsi], by rw [rd₄, rd₃, h₂.rd, rd₁], by rw [wr₄, wr₃, wr₂]⟩
  have a₂ := h₂.acc
  rw [firstBlock_ten, q₁] at a₂
  exact ⟨by rw [g₄ _ (by decide), g₃]; exact a₂.r8, by rw [g₄ _ (by decide), g₃]; exact a₂.r9,
    by rw [g₄ _ (by decide), g₃]; exact a₂.r10, by rw [g₄ _ (by decide), g₃]; exact a₂.h2,
    by simp only [hval, g₄ _ (show Reg.r11 ≠ .rsi by decide), g₄ _ (show Reg.rbx ≠ .rsi by decide),
      g₄ _ (show Reg.rbp ≠ .rsi by decide), g₃]; exact a₂.val⟩


/-- Before chunk `t` of `open`'s whole chunks, from the memory `m₀` on entry,
with the key `R0, R1` and the accumulator `A` on entry. -/
structure LO (c dp : Addr) (L : Nat) (R0 R1 : BitVec 64) (A : Nat) (m₀ : Mem) (sp : Addr)
    (t : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = bulkWr c dp L
  rdi : s.gpr .rdi = stA c
  rcx : s.gpr .rcx = bfA c
  rsi : s.gpr .rsi = dp + BitVec.ofNat 64 (512 * t)
  rsp : s.gpr .rsp = sp
  le : 512 * t ≤ L
  left : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t)
  cnt : stateAt s.mem (stA c) = ctr (stateAt m₀ (stA c)) (8 * t)
  data : ∀ k < L, s.mem (dp + BitVec.ofNat 64 k) =
    if k < 512 * t then m₀ (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt m₀ (stA c)) L).getD k 0
    else m₀ (dp + BitVec.ofNat 64 k)
  consts : Consts s.mem (bfA c)
  acc : Acc R0 R1 (absorbAll (rN R0 R1) A (bytesAt m₀ dp (512 * t))) s
  fr : Frame [stR (stA c), ⟨dp, L⟩, bufR (bfA c), ⟨slot (bfA c), 8⟩] m₀ s.mem

/-- The ciphertext of a chunk not yet decrypted is as it was on entry. -/
theorem LO.chunk_bytes {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr}
    {t : Nat} {s : State} (h : LO c dp L R0 R1 A m₀ sp t s) (hw : 512 * t + 512 ≤ L) :
    bytesAt s.mem (dp + BitVec.ofNat 64 (512 * t)) 512 = bytesAt m₀ (dp + BitVec.ofNat 64 (512 * t)) 512 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [Offset.add_add, h.data _ (by omega), ite_eq_right (by omega)]

/-- A chunk of `open`: the invariant from `t` to `t + 1`. -/
theorem chunkO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} (hge : 512 ≤ L - 512 * t) {s : State}
    (h : LO c dp L R0 R1 A m₀ sp t s) :
    WP isa chunkO s fun s' => LO c dp L R0 R1 A m₀ sp (t + 1) s' ∧
      s'.cf = some (decide (L - 512 * (t + 1) < 512)) := by
  have hLe := hl.L_lt
  have hw : 512 * t + 512 ≤ L := by omega
  have hq : dp + BitVec.ofNat 64 (512 * t) + 512 = dp + BitVec.ofNat 64 (512 * (t + 1)) := by
    have := window_eq dp (t := t + 1) (by omega); rwa [Nat.add_sub_cancel] at this
  have mst : stR (stA c) ∈ s.wr := by rw [h.wr]; simp
  have mbf : bufR (bfA c) ∈ s.wr := by rw [h.wr]; simp
  have md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hwd : DWin s.wr (dp + BitVec.ofNat 64 (512 * t)) := by
    intro off n hn
    exact ⟨_, md, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hin : ∀ off n, off + n ≤ 512 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 off) n := by
    intro off n hn
    exact ⟨_, List.mem_append_right _ md, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dsd : (stR (stA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) := hl.win_cd hw (by decide)
  have dbd : (bufR (bfA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) := hl.win_cd hw (by decide)
  have dqs : (dR5 (dp + BitVec.ofNat 64 (512 * t))).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right (win hw)).symm
  refine WP.seq (WP.mono (chunkMainO_ok hk h.rdi h.rcx h.rsi mst mbf hwd hin h.consts dsd st_bf dbd dqs h.acc)
    fun s₁ ⟨d₁, a₁, f₁, g₁, rsi₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at rsi₁
  have dslot : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))],
      (⟨slot (bfA c), 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_eq]
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · exact hl.win_cd hw (by decide)
  have sl₁ : s₁.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t) := by
    rw [f₁.readW (Region.contains_self _ _) dslot (by decide), h.left]
  refine WP.mono (next_ok (st := stA c) (buf := bfA c) (s := s₁) (by rw [g₁ _ (by decide) (by decide), h.rdi])
    (by rw [g₁ _ (by decide) (by decide), h.rcx]) (by rw [wr₁]; exact mst)
    ⟨psR c, by rw [wr₁, h.wr]; simp, slot_in⟩ st_slot
    (n := L - 512 * t) (by omega) hge sl₁)
    fun s₂ ⟨_, sl₂, cnt₂, f₂, g₂, rd₂, wr₂, _, _, cf₂⟩ => ?_
  have dst : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t))], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact dsd
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame f₁ dst
  have FA : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
      s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
  refine ⟨⟨by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr], by rw [g₂ _ (by decide) (by decide),
    g₁ _ (by decide) (by decide), h.rdi], by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rcx],
    by rw [g₂ _ (by decide) (by decide), rsi₁],
    by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rsp], by omega,
    by rw [sl₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega], ?_, ?_, ?_, ?_, ?_⟩,
    by rw [cf₂, show L - 512 * t - 512 = L - 512 * (t + 1) by omega]⟩
  · rw [cnt₂, S₁, h.cnt, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega]
  · intro k hk'
    have n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.st_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.ps_d _ (slot_ps _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.bf_d _ (slotsR_sub _ _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    rw [f₂ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact n_st
      · exact n_sl)]
    by_cases hin' : 512 * t ≤ k ∧ k < 512 * t + 512
    · have ea : dp + BitVec.ofNat 64 k =
          dp + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hin'.1]
      have x₁ := d₁ (k - 512 * t) (by omega)
      rw [← ea] at x₁
      rw [x₁, h.data k hk', ite_eq_right (by omega : ¬ k < 512 * t), ite_eq_left (by omega : k < 512 * (t + 1)),
        plus_block, h.cnt, ks_shift _ hk' hin'.1]
    · have n_w : ¬ (dR5 (dp + BitVec.ofNat 64 (512 * t))).Contains (dp + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]
        rw [Offset.sub_toNat' _ (by omega) (by omega)]
        split <;> omega
      rw [f₁ _ (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact n_sls
          · exact n_w), h.data k hk']
      by_cases hlt : k < 512 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega : k < 512 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k < 512 * (t + 1))]
  · refine h.consts.frame FA ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact (hl.bf_d.sub_left (hiR_sub _)).sub_right (win hw)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · rw [h.chunk_bytes hw, ← VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega),
      ← VG.Proof.Poly1305.bytesAt_add, show 512 * t + 512 = 512 * (t + 1) by omega] at a₁
    exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact a₁.r8, by rw [g₂ _ (by decide) (by decide)]; exact a₁.r9,
      by rw [g₂ _ (by decide) (by decide)]; exact a₁.r10, by rw [g₂ _ (by decide) (by decide)]; exact a₁.h2,
      by simp only [hval, g₂ _ (show Reg.r11 ≠ .rax by decide) (by decide),
        g₂ _ (show Reg.rbx ≠ .rax by decide) (by decide), g₂ _ (show Reg.rbp ≠ .rax by decide) (by decide)]
         exact a₁.val⟩
  · refine h.fr.trans (FA.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨⟨dp, L⟩, by simp, win hw⟩
    · exact ⟨stR (stA c), by simp, fun _ h => h⟩
    · exact ⟨⟨slot (bfA c), 8⟩, by simp, fun _ h => h⟩

/-- The chunks, while at least 512 bytes remain, from the first. -/
theorem chunksO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {s : State} (hge : 512 ≤ L) (h : LO c dp L R0 R1 A m₀ sp 0 s) :
    WP isa (.loop chunkO .ae) s fun s' => ∃ T, LO c dp L R0 R1 A m₀ sp T s' ∧ L - 512 * T < 512 := by
  let Inv : Nat → State → Prop := fun n s => ∃ u, n = L - 512 * u ∧ 512 ≤ L - 512 * u ∧
    LO c dp L R0 R1 A m₀ sp u s
  refine WP.loop (M := isa) Inv (fun n s ⟨u, hn, hu, hL⟩ => ?_) _ s ⟨0, rfl, by omega, h⟩
  refine WP.mono (chunkO_ok hl hk hu hL) fun s' ⟨hL', cf'⟩ => ?_
  by_cases hlt : L - 512 * (u + 1) < 512
  · exact .inl ⟨by simp [eval, cf', hlt], u + 1, hL', hlt⟩
  · exact .inr ⟨by simp [eval, cf', hlt], L - 512 * (u + 1), by omega, u + 1, rfl, by omega, hL'⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulkO`

`enter`, the chunks while 512 bytes remain, and `leaveO`. Of `L ≥ 512`
bytes of data, the first `512 T` are decrypted and their ciphertext (as on
entry) absorbed into the Poly1305 state, and `rbx`, `rbp` and `rsi`, `rdx`
are the rest.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps off)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)
open VG.Proof.Poly1305 (absorbAll)

theorem leaveO_eq : leaveO = Impl.Poly1305.X86_64.reduce ++ ([.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .mov .rdx (.mem (at_ .rcx lenOff)),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr) := rfl

theorem storeO_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block [.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .mov .rdx (.mem (at_ .rcx lenOff)),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]) s fun s' =>
      s'.mem = accMem s.mem c (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rbx = s.gpr .rsi ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
      s'.gpr .rdx = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .rdx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 →
        s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega) (by omega) (by decide)⟩
  have i : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, List.mem_append_right _ hw, Offset.contains c (by omega) (by omega) (by decide)⟩
  have o0 := o 448 (by decide) (by decide); have o1 := o 456 (by decide) (by decide)
  have o2 := o 464 (by decide) (by decide)
  have i0 := i 544 (by decide) (by decide); have i1 := i 520 (by decide) (by decide)
  have i2 := i 528 (by decide) (by decide); have i3 := i 536 (by decide) (by decide)
  apply WP.of_runBlock
  have se128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, State.store64,
    State.load64, readSrc, execAlu, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hrcx, accOff,
    r12Off, r13Off, r14Off, lenOff, ofInt_bf, Nat.reduceAdd, reduceCtorEq, o0, o1, o2, i0, i1, i2, i3,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 => by
    simp only [h1, h2, h3, h4, h5, h6, h7, ite_false], trivial, trivial⟩
  all_goals simp (disch := decide) only [readW_writeW_ofNat, se128, bfA, BitVec.add_sub_cancel]

theorem bulkO_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) {s : State}
    (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa bulkO s fun s' => ∃ T, 1 ≤ T ∧ 512 * T ≤ L ∧ L - 512 * T < 512 ∧
      (∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = if k < 512 * T then
        s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0
        else s.mem (dp + BitVec.ofNat 64 k)) ∧
      stateAt s'.mem (stA c) = ctr (stateAt s.mem (stA c)) (8 * T) ∧
      Repr s'.mem (psA c) key (msg ++ bytesAt s.mem dp (512 * T)) ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rsi = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdi = stA c ∧ s'.gpr .rcx = bfA c ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hLe := hl.L_lt
  unfold bulkO
  refine WP.seq (WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_)
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, hR0⟩ : ∃ R0, s.mem.readW (off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 = R0 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, s.mem.readW (off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 = R1 := ⟨_, rfl⟩
  have hk : Key R0 R1 := ⟨hR0 ▸ Proof.Poly1305.X86_64.r0_lt _, hR1 ▸ Proof.Poly1305.X86_64.r1_lt _,
    hR1 ▸ Proof.Poly1305.X86_64.r1_mod _⟩
  have hr : clamp (leNum (key.take 16)) = rN R0 R1 := by
    rw [← hrep.2.1, ← Proof.Poly1305.X86_64.off_24, Proof.Poly1305.X86_64.clamp_key, hR0, hR1]
  obtain ⟨A, hA⟩ : ∃ A, leNum (bytesAt s.mem (psA c) 24) = A := ⟨_, rfl⟩
  have hAm : A = accumulate (rN R0 R1) msg := by rw [← hA, hrep.2.2, hr]
  have hAP : A < P := hAm ▸ VG.Proof.Poly1305.accumulate_lt _ _
  have hA' := hA
  rw [Proof.Poly1305.X86_64.leNum_acc] at hA'
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst
  have ds : ∀ k < L, ∀ d n, d + n ≤ 576 → ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 :=
    fun k hk d n h hc => hl.cd h _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
  have e₁ : ∀ k < L, s₁.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k) := fun k hk => F₁ _ (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ds k hk 128 320 (by decide)
    · exact ds k hk 520 32 (by decide))
  have hd₁ : ∀ n, n ≤ L → bytesAt s₁.mem dp n = bytesAt s.mem dp n := fun n hn => by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => e₁ i (by have := List.mem_range.mp hi; omega)
  have h0 : LO c dp L R0 R1 A s₁.mem (s.gpr .rsp) 0 s₁ := by
    refine ⟨by rw [rd₁, hrd], by rw [wr₁, hwr], rdi₁, by rw [gk _ (.inl rfl), hrcx],
      by rw [gk _ (.inr (.inl rfl)), hrsi]; simp, gk _ (.inr (.inr rfl)), by omega,
      by rw [sl₁, hrdx, Nat.mul_zero, Nat.sub_zero], by simp [VG.Proof.ChaCha20.ctr_zero], fun k _ => by simp, C₁, ?_, Frame.refl _ _⟩
    rw [show 512 * 0 = 0 from rfl, show bytesAt s₁.mem dp 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    refine ⟨r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
    · have hP : P = 2 ^ 130 - 5 := rfl
      rw [rbp₁]; omega_using [hA', hAP, hP]
    · simp only [hval, r11₁, rbx₁, rbp₁, hA']
  refine WP.seq (WP.mono (chunksO_ok hl hk hge h0) fun s₃ ⟨T, L₃, hT⟩ => ?_)
  rw [leaveO_eq]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₃) fun s₄ ⟨red, k₄⟩ => ?_)
  refine WP.mono (storeO_ok (c := c) (s := s₄) (by rw [k₄.gpr', L₃.rcx]) (by rw [k₄.2.2.2, L₃.wr]; simp))
    fun s₅ ⟨m₅, rbx₅, rbp₅, rdx₅, r12₅, r13₅, r14₅, r15₅, g₅, rd₅, wr₅⟩ => ?_
  have hTL := L₃.le
  have hT1 : 1 ≤ T := by
    by_contra h'
    have : T = 0 := by omega
    subst this; omega
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have FA : Frame [accR c] s₃.mem s₅.mem := by rw [m₅, ← m₄]; exact accMem_frame _ _ _ _ _
  have S₅ : stateAt s₅.mem (stA c) = stateAt s₃.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame FA (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have st3 : ∀ d, 520 ≤ d → d + 8 ≤ 544 →
      s₃.mem.readW (c + BitVec.ofNat 64 d) 64 = s₁.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    refine L₃.fr.readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
    · exact hl.cd (by omega)
    · exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
    · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by omega)) (by omega) (by decide)
  have hkey : bytesAt s₅.mem (c + BitVec.ofNat 64 472) 32 = bytesAt s.mem (c + BitVec.ofNat 64 472) 32 := by
    have e₁ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) FA (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)) (by decide)
    have e₂ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) L₃.fr (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact hl.cd (by decide)
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
    have e₃ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) F₁ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [e₁, e₂, e₃]
  have hslot : s₄.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 (L - 512 * T) := by
    rw [m₄, ← slot_eq, L₃.left]
  have g5 : ∀ r : Reg, r = .rdi ∨ r = .rcx ∨ r = .rsp ∨ r = .rsi → s₅.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₄.gpr']
  refine ⟨T, hT1, hTL, hT, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [g5 _ (.inl rfl), L₃.rdi],
    by rw [g5 _ (.inr (.inl rfl)), L₃.rcx], ?_, ?_, ?_, r15₅, by rw [g5 _ (.inr (.inr (.inl rfl))), L₃.rsp],
    by rw [rd₅, k₄.2.2.1, L₃.rd, hrd], by rw [wr₅, k₄.2.2.2, L₃.wr, hwr]⟩
  · intro k hk
    rw [FA _ (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ds k hk 448 24 (by decide)),
      L₃.data k hk, e₁ k hk, S₁]
  · rw [S₅, L₃.cnt, S₁]
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hrep.1; omega
  · rw [psA_24, hkey, ← psA_24]; exact hrep.2.1
  · rw [m₅, accMem_acc]
    show hval s₄ = _
    rw [red L₃.acc.h2, L₃.acc.val, hd₁ _ hTL, hr, VG.Proof.Poly1305.accumulate_append hrep.1, ← hAm,
      Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt hAP _)]
  · rw [rbx₅, k₄.gpr', L₃.rsi]
  · rw [rbp₅, hslot]
  · rw [g5 _ (.inr (.inr (.inr rfl))), L₃.rsi]
  · rw [rdx₅, hslot]
  · rw [r12₅, m₄, st3 520 (by decide) (by decide), v12]
  · rw [r13₅, m₄, st3 528 (by decide) (by decide), v13]
  · rw [r14₅, m₄, st3 536 (by decide) (by decide), v14]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
