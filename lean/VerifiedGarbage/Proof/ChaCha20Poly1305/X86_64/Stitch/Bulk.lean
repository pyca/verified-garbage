import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Chunk

/-!
# ChaCha20 and Poly1305 together (x86-64): the whole chunks

`Stitch.bulk` proven with the permissions it needs (`bulkWr`): the ChaCha20
state at `c + 64`, the data, `buf` at `c + 128` and the Poly1305 state at
`c + 448`, of a context at `c` (`seal`'s), which `RegionModel.wp_narrow`
moves to `seal`'s permissions.

Before chunk `t` (`LI`), the first `512 t` bytes are encrypted, the counter
is advanced by `8 t`, the first `512 (t - 1)` bytes of ciphertext are
absorbed, and the bytes left are `L - 512 t`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR slotsR dR5 DWin hiR hiR_slots hiR_sub slotsR_sub
  plus_block ks_shift ctr_add)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact hf.bytes hd hn hi

section
variable (c : Addr)
/-- The ChaCha20 state, `buf` and the Poly1305 state, in the context at `c`. -/
abbrev stA : Addr := c + BitVec.ofNat 64 64
abbrev bfA : Addr := c + BitVec.ofNat 64 128
abbrev psA : Addr := c + BitVec.ofNat 64 448
abbrev psR : Region := ⟨psA c, 128⟩
end

/-- The permissions of the whole chunks. -/
abbrev bulkWr (c dp : Addr) (L : Nat) : List Region := [stR (stA c), ⟨dp, L⟩, bufR (bfA c), psR c]

/-- The context and the data: apart, and neither wrapping around. -/
structure Lay (c dp : Addr) (L : Nat) : Prop where
  L_lt : L < 2 ^ 64
  nowrap : dp.toNat + L ≤ 2 ^ 64
  dc : (⟨c, 576⟩ : Region).Disjoint ⟨dp, L⟩

section
variable {c dp : Addr} {L : Nat}

theorem sub_c {d n : Nat} (h : d + n ≤ 576) : Region.Sub ⟨c + BitVec.ofNat 64 d, n⟩ ⟨c, 576⟩ :=
  Offset.sub_base c h

theorem st_bf : (stR (stA c)).Disjoint (bufR (bfA c)) := Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)

theorem slot_eq : slot (bfA c) = c + BitVec.ofNat 64 544 := by
  rw [slot, Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]; rfl

theorem st_slot : (stR (stA c)).Disjoint ⟨slot (bfA c), 8⟩ := by
  rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)

theorem slot_ps : Region.Sub ⟨slot (bfA c), 8⟩ (psR c) := by
  rw [slot_eq]; exact Offset.sub c (by decide) (by decide)

theorem slot_in : (psR c).Contains (slot (bfA c)) 8 := by
  rw [slot_eq]; exact Offset.contains c (by decide) (by decide) (by decide)

/-- The window of chunk `t` is in the data. -/
theorem win {t : Nat} (h : 512 * t + 512 ≤ L) :
    Region.Sub (dR5 (dp + BitVec.ofNat 64 (512 * t))) ⟨dp, L⟩ := Offset.sub_base dp h

variable (hl : Lay c dp L)
include hl

theorem Lay.L_le : L ≤ 2 ^ 64 := Nat.le_of_lt hl.L_lt

theorem Lay.cd {d n : Nat} (h : d + n ≤ 576) : (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨dp, L⟩ :=
  hl.dc.sub_left (sub_c h)

theorem Lay.st_d : (stR (stA c)).Disjoint ⟨dp, L⟩ := hl.cd (by decide)
theorem Lay.bf_d : (bufR (bfA c)).Disjoint ⟨dp, L⟩ := hl.cd (by decide)
theorem Lay.ps_d : (psR c).Disjoint ⟨dp, L⟩ := hl.cd (by decide)

theorem Lay.win_cd {t : Nat} (h : 512 * t + 512 ≤ L) {d n : Nat} (hd : d + n ≤ 576) :
    (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * t))) :=
  (hl.cd hd).sub_right (win h)

end

/-- Before chunk `t` (`t ≥ 1`) of the whole chunks, from the memory `m₀`
on entry, with the key `R0, R1` and the accumulator `A` on entry, and the
values `v₁₂`, `v₁₃`, `v₁₄` stashed. -/
structure LI (c dp : Addr) (L : Nat) (R0 R1 : BitVec 64) (A : Nat) (m₀ : Mem) (sp : Addr)
    (t : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = bulkWr c dp L
  rdi : s.gpr .rdi = stA c
  rcx : s.gpr .rcx = bfA c
  rsi : s.gpr .rsi = dp + BitVec.ofNat 64 (512 * (t - 1))
  rsp : s.gpr .rsp = sp
  t1 : 1 ≤ t
  le : 512 * t ≤ L
  left : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 512 * t)
  cnt : stateAt s.mem (stA c) = ctr (stateAt m₀ (stA c)) (8 * t)
  data : ∀ k < L, s.mem (dp + BitVec.ofNat 64 k) =
    if k < 512 * t then m₀ (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt m₀ (stA c)) L).getD k 0
    else m₀ (dp + BitVec.ofNat 64 k)
  consts : Consts s.mem (bfA c)
  acc : Acc R0 R1 (absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * (t - 1)))) s
  fr : Frame [stR (stA c), ⟨dp, L⟩, bufR (bfA c), ⟨slot (bfA c), 8⟩] m₀ s.mem

theorem window_eq (dp : Addr) {t : Nat} (ht : 1 ≤ t) :
    dp + BitVec.ofNat 64 (512 * (t - 1)) + 512 = dp + BitVec.ofNat 64 (512 * t) := by
  rw [show (512 : Addr) = BitVec.ofNat 64 512 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 512 * (t - 1) + 512 = 512 * t by omega]

/-- A chunk: the loop invariant from `t` to `t + 1`. -/
theorem chunk_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} (hge : 512 ≤ L - 512 * t) {s : State}
    (h : LI c dp L R0 R1 A m₀ sp t s) :
    WP isa chunk s fun s' => LI c dp L R0 R1 A m₀ sp (t + 1) s' ∧
      s'.cf = some (decide (L - 512 * (t + 1) < 512)) := by
  have hLe := hl.L_lt
  have ht := h.t1
  have hw : 512 * t + 512 ≤ L := by omega
  have hq : dp + BitVec.ofNat 64 (512 * (t - 1)) + 512 = dp + BitVec.ofNat 64 (512 * t) := window_eq dp ht
  have wsub : Region.Sub (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)))) ⟨dp, L⟩ := win (t := t - 1) (by omega)
  have mst : stR (stA c) ∈ s.wr := by rw [h.wr]; simp
  have mbf : bufR (bfA c) ∈ s.wr := by rw [h.wr]; simp
  have md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hwd : DWin s.wr (dp + BitVec.ofNat 64 (512 * (t - 1)) + 512) := by
    rw [hq]; intro off n hn
    exact ⟨_, md, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hin : ∀ off n, off + n ≤ 512 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 (512 * (t - 1)) + BitVec.ofNat 64 off) n := by
    intro off n hn
    exact ⟨_, List.mem_append_right _ md, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dsd : (stR (stA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)) + 512)) := by
    rw [hq]; exact hl.win_cd hw (by decide)
  have dbd : (bufR (bfA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)) + 512)) := by
    rw [hq]; exact hl.win_cd hw (by decide)
  have dqs : (dR5 (dp + BitVec.ofNat 64 (512 * (t - 1)))).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right wsub).symm
  refine WP.seq (WP.mono (chunkMain_ok hk h.rdi h.rcx h.rsi mst mbf hwd hin h.consts dsd st_bf dbd dqs h.acc)
    fun s₁ ⟨d₁, a₁, f₁, g₁, rsi₁, rd₁, wr₁⟩ => ?_)
  rw [hq] at d₁ f₁ rsi₁
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
    · exact hl.win_cd hw (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame f₁ dst
  have FA : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
      s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
  refine ⟨⟨by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr], by rw [g₂ _ (by decide) (by decide),
    g₁ _ (by decide) (by decide), h.rdi], by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rcx],
    by rw [g₂ _ (by decide) (by decide), rsi₁, Nat.add_sub_cancel],
    by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), h.rsp], by omega, hw,
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
  · have F : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
        s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
    refine h.consts.frame F ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact (hl.bf_d.sub_left (hiR_sub _)).sub_right (win hw)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · have F : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 (512 * t)), stR (stA c), ⟨slot (bfA c), 8⟩]
        s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
    have hb : bytesAt s₂.mem dp (512 * t) = bytesAt s.mem dp (512 * t) := by
      refine bytesAt_frame F ?_ (by omega)
      have dsub : Region.Sub ⟨dp, 512 * t⟩ ⟨dp, L⟩ := Region.sub_prefix (by omega)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hl.bf_d.sub_left (slotsR_sub _)).symm.sub_left dsub
      · exact Offset.base_disjoint dp (Nat.le_refl _) (by omega)
      · exact hl.st_d.symm.sub_left dsub
      · exact (hl.ps_d.sub_left slot_ps).symm.sub_left dsub
    rw [Nat.add_sub_cancel, hb, show 512 * t = 512 * (t - 1) + 512 by omega, VG.Proof.Poly1305.bytesAt_add,
      VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega)]
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

/-- The first chunk, the kernel's: the loop invariant at 1. -/
theorem firstChunk_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} {A : Nat}
    {m₀ : Mem} {sp : Addr} (hge : 512 ≤ L) {s : State} (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L)
    (hrdi : s.gpr .rdi = stA c) (hrcx : s.gpr .rcx = bfA c) (hrsi : s.gpr .rsi = dp) (hrsp : s.gpr .rsp = sp)
    (hslot : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 L)
    (hm : s.mem = m₀)
    (hc : Consts s.mem (bfA c)) (hacc : Acc R0 R1 A s) :
    WP isa firstChunk s fun s' => LI c dp L R0 R1 A m₀ sp 1 s' ∧
      s'.cf = some (decide (L - 512 * 1 < 512)) := by
  have hLe := hl.L_lt
  have hcnt : stateAt s.mem (stA c) = stateAt m₀ (stA c) := by rw [hm]
  have hdata : ∀ k < L, s.mem (dp + BitVec.ofNat 64 k) = m₀ (dp + BitVec.ofNat 64 k) := fun _ _ => by rw [hm]
  have hw : 512 * 0 + 512 ≤ L := by omega
  have mst : stR (stA c) ∈ s.wr := by rw [hwr]; simp
  have mbf : bufR (bfA c) ∈ s.wr := by rw [hwr]; simp
  have md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have w0 : dp + BitVec.ofNat 64 (512 * 0) = dp := by simp
  unfold firstChunk firstMain
  refine WP.seq (WP.seq (WP.mono (Proof.ChaCha20.X86_64.Avx2.setup_ok hrdi hrcx mst mbf hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_))
  have c₁ : Consts s₁.mem (bfA c) := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR (bfA c)] s.mem s₁.mem := by
    rw [m₁]; exact Proof.ChaCha20.X86_64.Avx2.W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  refine WP.seq (WP.mono (Proof.ChaCha20.X86_64.Avx2.rounds_ok hh h15 (by rw [g₁, hrcx])
    (by rw [wr₁]; exact mbf) c₁.m8 10) fun s₂ hr => ?_)
  have F₂ := F₁.trans hr.frame
  have g₂ : s₂.gpr = s.gpr := hr.gpr.trans g₁
  have wr₂ : s₂.wr = s.wr := hr.wr.trans wr₁
  have dsd : (stR (stA c)).Disjoint (dR5 dp) := by
    have := hl.win_cd (t := 0) hw (d := 64) (n := 64) (by decide); rwa [w0] at this
  have dbd : (bufR (bfA c)).Disjoint (dR5 dp) := by
    have := hl.win_cd (t := 0) hw (d := 128) (n := 320) (by decide); rwa [w0] at this
  refine WP.mono (Proof.ChaCha20.X86_64.Avx2.finish_ok hr.holds (st := stA c) (by rw [g₂, hrdi])
    (by rw [g₂, hrcx]) (by rw [g₂, hrsi]) (by rw [wr₂]; exact mst) (by rw [wr₂]; exact mbf)
    (by rw [wr₂]; intro off n hn; exact ⟨_, md, Offset.contains_base _ (by omega) (by omega)⟩)
    (Proof.ChaCha20.X86_64.Avx2.incs_frame c₁.inc hr.frame (by
      intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hiR_slots _))
    dsd st_bf dbd) fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have F₃ : Frame [slotsR (bfA c), dR5 dp] s.mem s₃.mem := (F₂.mono (by simp)).trans f₃
  have dslot : ∀ r ∈ [slotsR (bfA c), dR5 dp], (⟨slot (bfA c), 8⟩ : Region).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl <;> rw [slot_eq]
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · have := hl.win_cd (t := 0) hw (d := 544) (n := 8) (by decide); rwa [w0] at this
  have sl₃ : s₃.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 L := by
    rw [F₃.readW (Region.contains_self _ _) dslot (by decide), hslot]
  refine WP.mono (next_ok (st := stA c) (buf := bfA c) (s := s₃) (by rw [g₃', hrdi]) (by rw [g₃', hrcx])
    (by rw [wr₃, wr₂]; exact mst) ⟨psR c, by rw [wr₃, wr₂, hwr]; simp, slot_in⟩ st_slot (n := L) hLe hge sl₃)
    fun s₄ ⟨_, sl₄, cnt₄, f₄, g₄, rd₄, wr₄, _, _, cf₄⟩ => ?_
  have dst : ∀ r ∈ [slotsR (bfA c), dR5 dp], (stR (stA c)).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact dsd
  have S₃ : stateAt s₃.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame F₃ dst
  have gk : ∀ r, r ≠ .rax → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b => by rw [g₄ r a b, g₃']
  refine ⟨⟨by rw [rd₄, rd₃, hr.rd, rd₁, hrd], by rw [wr₄, wr₃, wr₂, hwr], by rw [gk _ (by decide) (by decide), hrdi],
    by rw [gk _ (by decide) (by decide), hrcx], by rw [gk _ (by decide) (by decide), hrsi]; simp,
    by rw [gk _ (by decide) (by decide), hrsp], Nat.le_refl 1, by omega, by rw [sl₄], ?_, ?_, ?_, ?_, ?_⟩, by rw [cf₄]⟩
  · rw [cnt₄, S₃, hcnt, ← VG.Proof.ChaCha20.ctr_zero (stateAt m₀ (stA c)),
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add]
    simp only [VG.Proof.ChaCha20.ctr_zero, Nat.zero_add, Nat.mul_one]
  · intro k hk'
    have n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.st_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.ps_d _ (slot_ps _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
      hl.bf_d _ (slotsR_sub _ _ hc) (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    rw [f₄ _ (by
      intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact n_st
      · exact n_sl)]
    have S₂ : stateAt s₂.mem (stA c) = stateAt s.mem (stA c) :=
      Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using st_bf.sub_right (slotsR_sub (bfA c)))
    by_cases hin' : k < 512
    · have x₃ := d₃ k hin'
      rw [x₃, S₂, F₂ _ (by simpa using n_sls), hdata k hk', ite_eq_left (by omega : k < 512 * 1), plus_block,
        hcnt, VG.Proof.ChaCha20.keystream_getD _ hk']
    · have n_w : ¬ (dR5 dp).Contains (dp + BitVec.ofNat 64 k) 1 := by
        simp only [Region.Contains]
        rw [Mem.sub_ofNat_toNat dp (by omega)]
        omega
      rw [F₃ _ (by
          intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl
          · exact n_sls
          · exact n_w), hdata k hk', ite_eq_right (by omega : ¬ k < 512 * 1)]
  · have F : Frame [slotsR (bfA c), dR5 dp, stR (stA c), ⟨slot (bfA c), 8⟩] s.mem s₄.mem :=
      (F₃.mono (by simp)).trans (f₄.mono (by simp))
    refine hc.frame F ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact dbd.sub_left (hiR_sub _)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · rw [show 512 * (1 - 1) = 0 from rfl, show bytesAt s₄.mem dp 0 = [] from rfl,
      VG.Proof.Poly1305.absorbAll_nil]
    exact ⟨by rw [gk _ (by decide) (by decide)]; exact hacc.r8, by rw [gk _ (by decide) (by decide)]; exact hacc.r9,
      by rw [gk _ (by decide) (by decide)]; exact hacc.r10, by rw [gk _ (by decide) (by decide)]; exact hacc.h2,
      by simp only [hval, gk _ (show Reg.r11 ≠ .rax by decide) (by decide),
        gk _ (show Reg.rbx ≠ .rax by decide) (by decide), gk _ (show Reg.rbp ≠ .rax by decide) (by decide)]
         exact hacc.val⟩
  · rw [← hm]
    have FA : Frame [slotsR (bfA c), dR5 dp, stR (stA c), ⟨slot (bfA c), 8⟩] s.mem s₄.mem :=
      (F₃.mono (by simp)).trans (f₄.mono (by simp))
    refine FA.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨⟨dp, L⟩, by simp, by have := win (dp := dp) (t := 0) hw; rwa [w0] at this⟩
    · exact ⟨stR (stA c), by simp, fun _ h => h⟩
    · exact ⟨⟨slot (bfA c), 8⟩, by simp, fun _ h => h⟩

/-- The later chunks, while at least 512 bytes remain. -/
theorem chunks_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {t : Nat} {s : State} (h : LI c dp L R0 R1 A m₀ sp t s)
    (hcf : s.cf = some (decide (L - 512 * t < 512))) :
    WP isa (.ite .b (.block []) (.loop chunk .ae)) s fun s' =>
      ∃ T, LI c dp L R0 R1 A m₀ sp T s' ∧ L - 512 * T < 512 := by
  refine WP.ite (decide (L - 512 * t < 512)) (by simp only [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨t, h, by simpa using hb⟩
  · have hge : 512 ≤ L - 512 * t := by simp at hb; omega
    let Inv : Nat → State → Prop := fun n s => ∃ u, n = L - 512 * u ∧ 512 ≤ L - 512 * u ∧
      LI c dp L R0 R1 A m₀ sp u s
    refine WP.loop (M := isa) Inv (fun n s ⟨u, hn, hu, hL⟩ => ?_) _ s ⟨t, rfl, hge, h⟩
    refine WP.mono (chunk_ok hl hk hu hL) fun s' ⟨hL', cf'⟩ => ?_
    by_cases hlt : L - 512 * (u + 1) < 512
    · exact .inl ⟨by simp [eval, cf', hlt], u + 1, hL', hlt⟩
    · exact .inr ⟨by simp [eval, cf', hlt], L - 512 * (u + 1), by omega, u + 1, rfl, by omega, hL'⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): entering and leaving the chunks

`Stitch.enter` stashes `r12`–`r14` and the length, stores the kernel's
constants (`Avx2.pairs_ok`) and loads the key and the accumulator from the
Poly1305 state (`Poly1305.X86_64.setup_ok`); `Stitch.leave` reduces the
accumulator (`reduce_ok`), stores it, and restores the stashed registers.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.Poly1305.X86_64 (hval Keeps)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (P bytesAt)

/-- The stash, in the Poly1305 state's working space. -/
abbrev stashR (c : Addr) : Region := ⟨c + BitVec.ofNat 64 520, 32⟩

theorem ofInt_bf (c : Addr) (d : Nat) :
    bfA c + BitVec.ofInt 64 ((d : Nat) : Int) = c + BitVec.ofNat 64 (128 + d) := by
  rw [Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_writeW_ofNat (m : Mem) (c : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (c + BitVec.ofNat 64 e) v).readW (c + BitVec.ofNat 64 d) 64 = m.readW (c + BitVec.ofNat 64 d) 64 := by
  have := Proof.Poly1305.X86_64.readW_writeW_off m c v hd he h
  simpa only [Proof.Poly1305.X86_64.off, Proof.Poly1305.X86_64.ofInt_natCast] using this

set_option simprocs false in
theorem stash_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block [.store (at_ .rcx r12Off) .r12, .store (at_ .rcx r13Off) .r13,
      .store (at_ .rcx r14Off) .r14, .store (at_ .rcx lenOff) .rdx]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [stashR c] s.mem s'.mem ∧
      s'.mem.readW (c + BitVec.ofNat 64 520) 64 = s.gpr .r12 ∧
      s'.mem.readW (c + BitVec.ofNat 64 528) 64 = s.gpr .r13 ∧
      s'.mem.readW (c + BitVec.ofNat 64 536) 64 = s.gpr .r14 ∧
      s'.mem.readW (c + BitVec.ofNat 64 544) 64 = s.gpr .rdx := by
  have o : ∀ d, 520 ≤ d → d + 8 ≤ 552 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega) (by omega) (by decide)⟩
  have cs : ∀ d, 520 ≤ d → d + 8 ≤ 552 → (stashR c).Contains (c + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains c (by omega) (by omega) (by decide)
  have o0 := o 520 (by decide) (by decide); have o1 := o 528 (by decide) (by decide)
  have o2 := o 536 (by decide) (by decide); have o3 := o 544 (by decide) (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, State.store64,
    hrcx, r12Off, r13Off, r14Off, lenOff, ofInt_bf, o0, o1, o2, o3, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cs 520 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cs 528 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (cs 536 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (cs 544 (by decide) (by decide))
  all_goals simp (disch := decide) only [readW_writeW_ofNat, Mem.readW_writeW_self64]

set_option simprocs false in
/-- `rdi = rcx + d` (`d` 320) or `rcx - d` (`d` 64). -/
theorem rdiAdd_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) :
    WP isa (.block [.mov .rdi (.reg .rcx), .alu .add .rdi (.imm 320)]) s fun s' =>
      s'.gpr .rdi = psA c ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨?_, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial⟩
  rw [hrcx, show BitVec.signExtend 64 (320 : BitVec 32) = BitVec.ofNat 64 320 by decide, BitVec.add_assoc,
    ← BitVec.ofNat_add]

set_option simprocs false in
theorem rdiSub_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) :
    WP isa (.block [.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)]) s fun s' =>
      s'.gpr .rdi = stA c ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    State.setReg, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨?_, fun r hr => by simp [hr], trivial, trivial, trivial, trivial, trivial⟩
  rw [hrcx, show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 64 by decide,
    BitVec.sub_eq_iff_eq_add, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A word of the Poly1305 state (`[0, 40)`: the accumulator and `r`) is
apart from the stash and `buf`. -/
theorem ps_word {c : Addr} {m m' : Mem} (hf : Frame [bufR (bfA c), stashR c] m m') {d : Nat} (hd : d + 8 ≤ 40) :
    m'.readW (Proof.Poly1305.X86_64.off (psA c) d) 64 = m.readW (Proof.Poly1305.X86_64.off (psA c) d) 64 := by
  have e : Proof.Poly1305.X86_64.off (psA c) d = c + BitVec.ofNat 64 (448 + d) := by
    rw [Proof.Poly1305.X86_64.off, Proof.Poly1305.X86_64.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine hf.readW (r := ⟨c + BitVec.ofNat 64 (448 + d), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
  · exact Offset.disjoint c (Or.inl (by omega)) (by omega) (by decide)

theorem enter_eq : enter = ([.store (at_ .rcx r12Off) .r12, .store (at_ .rcx r13Off) .r13,
    .store (at_ .rcx r14Off) .r14, .store (at_ .rcx lenOff) .rdx] : List Instr) ++
    (Impl.ChaCha20.X86_64.Avx2.consts ++ (([.mov .rdi (.reg .rcx), .alu .add .rdi (.imm 320)] : List Instr) ++
    (Impl.Poly1305.X86_64.setup ++ ([.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)] : List Instr)))) := by
  simp only [enter, List.append_assoc, List.cons_append, List.nil_append]

theorem enter_ok {c dp : Addr} {L : Nat} {s : State} (hwr : s.wr = bulkWr c dp L)
    (hrcx : s.gpr .rcx = bfA c) :
    WP isa (.block enter) s fun s' =>
      s'.gpr .rdi = stA c ∧ (∀ r, r ≠ .rdi → r ≠ .rax → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rbx → r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [bufR (bfA c), stashR c] s.mem s'.mem ∧ Consts s'.mem (bfA c) ∧
      s'.mem.readW (slot (bfA c)) 64 = s.gpr .rdx ∧
      s'.mem.readW (c + BitVec.ofNat 64 520) 64 = s.gpr .r12 ∧
      s'.mem.readW (c + BitVec.ofNat 64 528) 64 = s.gpr .r13 ∧
      s'.mem.readW (c + BitVec.ofNat 64 536) 64 = s.gpr .r14 ∧
      s'.gpr .r8 = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 ∧
      s'.gpr .r9 = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 ∧
      (s'.gpr .r10).toNat = 5 * ((s'.gpr .r9).toNat / 4) ∧
      s'.gpr .r11 = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 0) 64 ∧
      s'.gpr .rbx = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 8) 64 ∧
      s'.gpr .rbp = s.mem.readW (Proof.Poly1305.X86_64.off (psA c) 16) 64 := by
  rw [enter_eq]
  refine WP.block_append (WP.mono (stash_ok hrcx (by rw [hwr]; simp))
    fun s₁ ⟨g₁, rd₁, wr₁, f₁, v12, v13, v14, vl⟩ => ?_)
  rw [Proof.ChaCha20.X86_64.Avx2.consts_eq]
  refine WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2.pairs_ok (buf := bfA c)
    Proof.ChaCha20.X86_64.Avx2.constPairs Proof.ChaCha20.X86_64.Avx2.constPairs_le (s := s₁)
    (by rw [g₁, hrcx]) (by rw [wr₁, hwr]; simp)) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (rdiAdd_ok (c := c) (by rw [g₂ _ (by decide), g₁, hrcx]))
    fun s₃ ⟨rdi₃, g₃, m₃, rd₃, wr₃, _, _⟩ => ?_)
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.setup_ok s₃ (by rw [rdi₃, wr₃, wr₂, wr₁, hwr, rd₃, rd₂, rd₁]; simp))
    fun s₄ ⟨r8, r9, r10, r11, rbx, rbp, k₄⟩ => ?_)
  refine WP.mono (rdiSub_ok (c := c) (by rw [k₄.gpr' (r := .rcx), g₃ _ (by decide), g₂ _ (by decide), g₁, hrcx]))
    fun s₅ ⟨rdi₅, g₅, m₅, rd₅, wr₅, _, _⟩ => ?_
  have F₂ : Frame [bufR (bfA c), stashR c] s.mem s₂.mem := by
    rw [m₂]
    exact (f₁.mono (by simp)).trans
      (Proof.ChaCha20.X86_64.Avx2.storeAll_frame (by simp) _ Proof.ChaCha20.X86_64.Avx2.constPairs_le _)
  have mm : s₅.mem = s₂.mem := by rw [m₅, k₄.2.1, m₃]
  have dsl : ∀ d, 520 ≤ d → d + 8 ≤ 552 → s₅.mem.readW (c + BitVec.ofNat 64 d) 64 = s₁.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [mm, m₂]
    refine (Proof.ChaCha20.X86_64.Avx2.storeAll_frame (List.mem_singleton_self _) _
      Proof.ChaCha20.X86_64.Avx2.constPairs_le _).readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
  have g4 : ∀ r, r ∉ [Reg.rax, .r8, .r9, .r10, .r11, .rbx, .rbp] → s₄.gpr r = s₃.gpr r := k₄.1
  refine ⟨rdi₅, fun r h1 h2 h3 h4 h5 h6 h7 h8 => ?_, by rw [rd₅, k₄.2.2.1, rd₃, rd₂, rd₁],
    by rw [wr₅, k₄.2.2.2, wr₃, wr₂, wr₁], by rw [mm]; exact F₂,
    by rw [mm, m₂]; exact Proof.ChaCha20.X86_64.Avx2.consts_mem _ _,
    by rw [slot_eq, dsl 544 (by decide) (by decide), vl],
    by rw [dsl 520 (by decide) (by decide), v12], by rw [dsl 528 (by decide) (by decide), v13],
    by rw [dsl 536 (by decide) (by decide), v14], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₅ r h1, g4 r (by simp [h2, h3, h4, h5, h6, h7, h8]), g₃ r h1, g₂ r h2, g₁]
  · rw [g₅ _ (by decide), r8, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), r9, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), g₅ _ (by decide)]; exact r10
  · rw [g₅ _ (by decide), r11, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), rbx, rdi₃, m₃, ps_word F₂ (by decide)]
  · rw [g₅ _ (by decide), rbp, rdi₃, m₃, ps_word F₂ (by decide)]

theorem leave_eq : leave = Impl.Poly1305.X86_64.reduce ++ ([.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .alu .add .rbp (.imm 512),
    .mov .rdx (.mem (at_ .rcx lenOff)), .alu .add .rsi (.imm 512),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr) := rfl

/-- The accumulator stored, as `storeH` would at `psA c`. -/
abbrev accMem (m : Mem) (c : Addr) (h0 h1 h2 : BitVec 64) : Mem :=
  ((m.writeW (c + BitVec.ofNat 64 448) h0).writeW (c + BitVec.ofNat 64 456) h1).writeW
    (c + BitVec.ofNat 64 464) h2

theorem store_ok {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block [.store (at_ .rcx accOff) .r11,
    .store (at_ .rcx (accOff + 8)) .rbx, .store (at_ .rcx (accOff + 16)) .rbp,
    .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .alu .add .rbp (.imm 512),
    .mov .rdx (.mem (at_ .rcx lenOff)), .alu .add .rsi (.imm 512),
    .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
    .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]) s fun s' =>
      s'.mem = accMem s.mem c (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rbx = s.gpr .rsi ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 + 512 ∧
      s'.gpr .rdx = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧ s'.gpr .rsi = s.gpr .rsi + 512 ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .rdx → r ≠ .rsi → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 →
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
  have se512 : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  have se128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, State.store64,
    State.load64, readSrc, execAlu, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hrcx, accOff,
    r12Off, r13Off, r14Off, lenOff, ofInt_bf, Nat.reduceAdd, reduceCtorEq, o0, o1, o2, i0, i1, i2, i3,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false], trivial, trivial⟩
  all_goals simp (disch := decide) only [readW_writeW_ofNat, se512, se128, bfA, BitVec.add_sub_cancel]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulk`

`Stitch.bulk`, with the permissions it needs (`bulkWr`): `enter`, the first
chunk, the later ones while 512 bytes remain, and `leave`. Of `L ≥ 512`
bytes of data, the first `512 T` are encrypted, the first `512 (T - 1)` are
absorbed into the Poly1305 state, which represents the message before them
followed by them, and `rbx`, `rbp` are the ciphertext not yet absorbed and
`rsi`, `rdx` the data not yet encrypted.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps off)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)
open VG.Proof.Poly1305 (absorbAll)

/-- The accumulator's region in the Poly1305 state. -/
abbrev accR (c : Addr) : Region := ⟨c + BitVec.ofNat 64 448, 24⟩

theorem accMem_frame (m : Mem) (c : Addr) (h0 h1 h2 : BitVec 64) :
    Frame [accR c] m (accMem m c h0 h1 h2) := by
  have ca : ∀ d, 448 ≤ d → d + 8 ≤ 472 → (accR c).Contains (c + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains c (by omega) (by omega) (by decide)
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ca 448 (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (ca 456 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (ca 464 (by decide) (by decide))

theorem psA_24 (c : Addr) : psA c + 24 = c + BitVec.ofNat 64 472 := by
  rw [psA, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_ps (c : Addr) (d : Nat) : off (psA c) d = c + BitVec.ofNat 64 (448 + d) := by
  rw [Proof.Poly1305.X86_64.off_eq, psA, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem accMem_acc (m : Mem) (c : Addr) (h0 h1 h2 : BitVec 64) :
    leNum (bytesAt (accMem m c h0 h1 h2) (psA c) 24) = h0.toNat + 2 ^ 64 * h1.toNat + 2 ^ 128 * h2.toNat := by
  rw [Proof.Poly1305.X86_64.leNum_acc, off_ps, off_ps, off_ps]
  simp (disch := decide) only [accMem, Nat.reduceAdd, readW_writeW_ofNat, Mem.readW_writeW_self64]

theorem bulk_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) {s : State}
    (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa bulk s fun s' => ∃ T, 1 ≤ T ∧ 512 * T ≤ L ∧ L - 512 * T < 512 ∧
      (∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = if k < 512 * T then
        s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0
        else s.mem (dp + BitVec.ofNat 64 k)) ∧
      stateAt s'.mem (stA c) = ctr (stateAt s.mem (stA c)) (8 * T) ∧
      Repr s'.mem (psA c) key (msg ++ bytesAt s'.mem dp (512 * (T - 1))) ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * (T - 1)) ∧
      s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * (T - 1)) ∧
      s'.gpr .rsi = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdi = stA c ∧ s'.gpr .rcx = bfA c ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hLe := hl.L_lt
  unfold bulk
  refine WP.seq (WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_)
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The key and the accumulator.
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
  have acc₁ : Acc R0 R1 A s₁ := by
    refine ⟨r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
    · have hP : P = 2 ^ 130 - 5 := rfl
      rw [rbp₁]; omega_using [hA', hAP, hP]
    · simp only [hval, r11₁, rbx₁, rbp₁, hA']
  refine WP.seq (WP.mono (firstChunk_ok hl (R0 := R0) (R1 := R1) (A := A) (m₀ := s₁.mem) (sp := s.gpr .rsp)
    hge (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) rdi₁ (by rw [gk _ (.inl rfl), hrcx])
    (by rw [gk _ (.inr (.inl rfl)), hrsi]) (gk _ (.inr (.inr rfl))) (by rw [sl₁, hrdx]) rfl C₁ acc₁)
    fun s₂ ⟨L₂, cf₂⟩ => ?_)
  refine WP.seq (WP.mono (chunks_ok hl hk L₂ cf₂) fun s₃ ⟨T, L₃, hT⟩ => ?_)
  rw [leave_eq]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₃) fun s₄ ⟨red, k₄⟩ => ?_)
  refine WP.mono (store_ok (c := c) (s := s₄) (by rw [k₄.gpr', L₃.rcx]) (by rw [k₄.2.2.2, L₃.wr]; simp))
    fun s₅ ⟨m₅, rbx₅, rbp₅, rdx₅, rsi₅, r12₅, r13₅, r14₅, r15₅, g₅, rd₅, wr₅⟩ => ?_
  have ht := L₃.t1
  have hTL := L₃.le
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have FA : Frame [accR c] s₃.mem s₅.mem := by rw [m₅, ← m₄]; exact accMem_frame _ _ _ _ _
  -- What the context's regions keep.
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst
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
  have dsub : Region.Sub ⟨dp, 512 * (T - 1)⟩ ⟨dp, L⟩ := Region.sub_prefix (by omega)
  have hb : bytesAt s₅.mem dp (512 * (T - 1)) = bytesAt s₃.mem dp (512 * (T - 1)) := by
    refine bytesAt_frame FA ?_ (by omega)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hl.cd (d := 448) (n := 24) (by decide)).symm.sub_left dsub
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
  have e512 : ∀ n, n + 512 < 2 ^ 64 →
      BitVec.ofNat 64 n + 512 = BitVec.ofNat 64 (n + 512) := fun n _ => by
    rw [show (512 : Addr) = BitVec.ofNat 64 512 from rfl, ← BitVec.ofNat_add]
  have g5 : ∀ r : Reg, r = .rdi ∨ r = .rcx ∨ r = .rsp → s₅.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        k₄.gpr']
  refine ⟨T, ht, hTL, hT, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [g5 _ (.inl rfl), L₃.rdi],
    by rw [g5 _ (.inr (.inl rfl)), L₃.rcx], ?_, ?_, ?_, r15₅, by rw [g5 _ (.inr (.inr rfl)), L₃.rsp],
    by rw [rd₅, k₄.2.2.1, L₃.rd, hrd], by rw [wr₅, k₄.2.2.2, L₃.wr, hwr]⟩
  · intro k hk
    have ds : ∀ d n, d + n ≤ 576 → ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 :=
      fun d n h hc => hl.cd h _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
    have e₁ : s₁.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k) := F₁ _ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ds 128 320 (by decide)
      · exact ds 520 32 (by decide))
    rw [FA _ (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ds 448 24 (by decide)),
      L₃.data k hk, e₁, S₁]
  · rw [S₅, L₃.cnt, S₁]
  · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hrep.1; omega
  · rw [psA_24, hkey, ← psA_24]; exact hrep.2.1
  · rw [m₅, accMem_acc, ← m₅]
    show hval s₄ = _
    rw [red L₃.acc.h2, L₃.acc.val, hb, hr, VG.Proof.Poly1305.accumulate_append hrep.1, ← hAm,
      Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt hAP _)]
  · rw [rbx₅, k₄.gpr', L₃.rsi]
  · rw [rbp₅, hslot, e512 _ (by omega), show L - 512 * T + 512 = L - 512 * (T - 1) by omega]
  · rw [rsi₅, k₄.gpr', L₃.rsi, window_eq dp ht]
  · rw [rdx₅, hslot]
  · rw [r12₅, m₄, st3 520 (by decide) (by decide), v12]
  · rw [r13₅, m₄, st3 528 (by decide) (by decide), v13]
  · rw [r14₅, m₄, st3 536 (by decide) (by decide), v14]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
