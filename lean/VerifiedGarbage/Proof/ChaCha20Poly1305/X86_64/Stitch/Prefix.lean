module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 and Poly1305 together (x86-64): the 448 bytes before the chunks

When the prologue computes the keystream of the first 448 bytes too
(`splitM` for `pass` 512), `cryptPre` encrypts them, and the rest is whole
chunks and 1 to 448 bytes, or 1 to 512 bytes without a chunk. `Stitch.bulkP` encrypts the chunks after the 448
bytes, the first of which absorbs those (`chunk true`, `chunkP_ok`): from
there on the code is `bulk`'s on the data after the 448 bytes (`restLI_ok`,
on narrower permissions), whose accumulator on entry is the 448 bytes'
absorbed. Without whole chunks, `tailS` or `tailKX` encrypts the rest while
it absorbs the 448 bytes (`tailPS_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR slotsR dR5 hiR_slots hiR_sub slotsR_sub plus_block ctr_add)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305.X86_64 (hval off)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)
open VG.Proof.Poly1305 (absorbAll)
open VG.Impl.ChaCha20.X86_64 (at_)

theorem total_true : 16 * total true = 448 := rfl
theorem tot_true : tot true = BitVec.ofNat 64 448 := rfl

/-- The data after its first `o` bytes. -/
theorem Lay.shift {c dp : Addr} {L : Nat} (hl : Lay c dp L) {o : Nat} (ho : o ≤ L) :
    Lay c (dp + BitVec.ofNat 64 o) (L - o) := by
  have hLe := hl.L_lt
  refine ⟨by omega_arith, ?_, hl.dc.sub_right (Offset.sub_base dp (by omega_arith))⟩
  have := hl.nowrap
  have : (dp + BitVec.ofNat 64 o).toNat ≤ dp.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega_arith)]
    exact Nat.mod_le _ _
  omega_arith

/-- The first chunk after the 448 bytes before it, which it absorbs: the loop
invariant at 1 of the data after the 448 (on the permissions of that data),
with the 448 absorbed into the accumulator on entry. -/
theorem chunkP_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} (hge : 960 ≤ L) {s : State} (hwr : s.wr = bulkWr c dp L)
    (hrdi : s.gpr .rdi = stA c) (hrcx : s.gpr .rcx = bfA c) (hrsi : s.gpr .rsi = dp) (hrsp : s.gpr .rsp = sp)
    (hslot : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 448))
    (hm : s.mem = m₀) (hc : Consts s.mem (bfA c)) (hacc : Acc R0 R1 A s) :
    WP isa (chunk vl true) s fun s' =>
      LI c (dp + BitVec.ofNat 64 448) (L - 448) R0 R1 (absorbAll (rN R0 R1) A (bytesAt m₀ dp 448)) m₀ sp 1
        (s'.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448))) ∧
      s'.cf = some (decide (L - 448 - 512 * 1 < 512)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 448), stR (stA c), ⟨slot (bfA c), 8⟩] s.mem s'.mem := by
  have hLe := hl.L_lt
  have hl' := hl.shift (o := 448) (by omega_arith)
  have hw : 448 + 512 ≤ L := by omega_arith
  have wsub : Region.Sub (dR5 (dp + BitVec.ofNat 64 448)) ⟨dp, L⟩ := Offset.sub_base dp hw
  have wsub' : Region.Sub (dR5 (dp + BitVec.ofNat 64 448)) ⟨dp + BitVec.ofNat 64 448, L - 448⟩ :=
    Region.sub_prefix (by omega_arith)
  have mst : stR (stA c) ∈ s.wr := by rw [hwr]; simp
  have mbf : bufR (bfA c) ∈ s.wr := by rw [hwr]; simp
  have md : (⟨dp, L⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hwd : Proof.ChaCha20.X86_64.Avx2.DWin s.wr (dp + tot true) := by
    rw [tot_true]; intro off n hn
    exact ⟨_, md, by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hin : ∀ off n, off + n ≤ 512 → InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 off) n := by
    intro off n hn
    exact ⟨_, List.mem_append_right _ md, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have dsd : (stR (stA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 448)) := (hl.cd (by decide)).sub_right wsub
  have dbd : (bufR (bfA c)).Disjoint (dR5 (dp + BitVec.ofNat 64 448)) := (hl.cd (by decide)).sub_right wsub
  have dqs : (dR5 dp).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right (Region.sub_prefix (by omega_arith))).symm
  refine WP.seq (WP.mono (chunkMain_ok vl true hk hrdi hrcx hrsi mst mbf hwd hin hc
    (by rw [tot_true]; exact dsd) st_bf (by rw [tot_true]; exact dbd) dqs hacc)
    fun s₁ ⟨d₁, a₁, f₁, g₁, rsi₁, rd₁, wr₁⟩ => ?_)
  rw [tot_true] at d₁ f₁ rsi₁
  rw [total_true] at a₁
  have dslot : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 448)],
      (⟨slot (bfA c), 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [slot_eq]
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · exact (hl.cd (by decide)).sub_right wsub
  have sl₁ : s₁.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 (L - 448) := by
    rw [f₁.readW (Region.contains_self _ _) dslot (by decide), hslot]
  refine WP.mono (next_ok (st := stA c) (buf := bfA c) (s := s₁) (by rw [g₁ _ (by decide) (by decide), hrdi])
    (by rw [g₁ _ (by decide) (by decide), hrcx]) (by rw [wr₁]; exact mst)
    ⟨psR c, by rw [wr₁, hwr]; simp, slot_in⟩ st_slot
    (n := L - 448) (by omega_arith) (by omega_arith) sl₁)
    fun s₂ ⟨_, sl₂, cnt₂, f₂, g₂, rd₂, wr₂, _, _, cf₂⟩ => ?_
  have dst : ∀ r ∈ [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 448)], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf.sub_right (slotsR_sub _)
    · exact dsd
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame f₁ dst
  have FA : Frame [slotsR (bfA c), dR5 (dp + BitVec.ofNat 64 448), stR (stA c), ⟨slot (bfA c), 8⟩]
      s.mem s₂.mem := (f₁.mono (by simp)).trans (f₂.mono (by simp))
  have gk : ∀ r, r ∉ Proof.Poly1305.X86_64.absorbRegs → r ≠ .rsi → r ≠ .rax → r ≠ .rdx →
      s₂.gpr r = s.gpr r := fun r a b c' d => by rw [g₂ r c' d, g₁ r a b]
  refine ⟨⟨by simp, by simp, by rw [State.withRegions_gpr, gk _ (by decide) (by decide) (by decide) (by decide), hrdi],
    by rw [State.withRegions_gpr, gk _ (by decide) (by decide) (by decide) (by decide), hrcx],
    by rw [State.withRegions_gpr, g₂ _ (by decide) (by decide), rsi₁]; simp,
    by rw [State.withRegions_gpr, gk _ (by decide) (by decide) (by decide) (by decide), hrsp], Nat.le_refl 1,
    by omega_arith, by rw [State.withRegions_mem, sl₂], ?_, ?_, ?_, ?_, ?_⟩,
    by rw [cf₂], by rw [rd₂, rd₁], by rw [wr₂, wr₁], FA⟩
  · rw [State.withRegions_mem, cnt₂, S₁, ← hm, ← VG.Proof.ChaCha20.ctr_zero (stateAt s.mem (stA c)),
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, ctr_add]
    simp only [VG.Proof.ChaCha20.ctr_zero, Nat.zero_add, Nat.mul_one]
  · intro k hk'
    rw [State.withRegions_mem]
    have hk'' : 448 + k < L := by omega_arith
    have ea : dp + BitVec.ofNat 64 448 + BitVec.ofNat 64 k = dp + BitVec.ofNat 64 (448 + k) := Offset.add_add _ _ _
    have n_st : ¬ (stR (stA c)).Contains (dp + BitVec.ofNat 64 (448 + k)) 1 := fun hc' =>
      hl.st_d _ hc' (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    have n_sl : ¬ (⟨slot (bfA c), 8⟩ : Region).Contains (dp + BitVec.ofNat 64 (448 + k)) 1 := fun hc' =>
      hl.ps_d _ (slot_ps _ hc') (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    have n_sls : ¬ (slotsR (bfA c)).Contains (dp + BitVec.ofNat 64 (448 + k)) 1 := fun hc' =>
      hl.bf_d _ (slotsR_sub _ _ hc') (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
    rw [ea, f₂ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact n_st
      · exact n_sl), ← hm]
    by_cases hin' : k < 512
    · have x₁ := d₁ k hin'
      rw [ea] at x₁
      rw [x₁, ite_eq_left (by omega_arith : k < 512 * 1), plus_block, VG.Proof.ChaCha20.keystream_getD _ hk']
    · have n_w : ¬ (dR5 (dp + BitVec.ofNat 64 448)).Contains (dp + BitVec.ofNat 64 (448 + k)) 1 := by
        rw [← ea]
        simp only [Region.Contains]
        rw [Mem.sub_ofNat_toNat _ (by omega_arith)]
        omega_arith
      rw [f₁ _ (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact n_sls
          · exact n_w), ite_eq_right (by omega_arith : ¬ k < 512 * 1)]
  · rw [State.withRegions_mem]
    refine hc.frame FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact hiR_slots _
    · exact dbd.sub_left (hiR_sub _)
    · exact (st_bf.symm.sub_left (hiR_sub _))
    · exact ((Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide) :
        (bufR (bfA c)).Disjoint (psR c)).sub_left (hiR_sub _)).sub_right slot_ps
  · rw [show 512 * (1 - 1) = 0 from rfl, show bytesAt (s₂.withRegions [] _).mem _ 0 = [] from rfl,
      VG.Proof.Poly1305.absorbAll_nil, ← hm]
    exact ⟨by rw [State.withRegions_gpr, g₂ _ (by decide) (by decide)]; exact a₁.r8,
      by rw [State.withRegions_gpr, g₂ _ (by decide) (by decide)]; exact a₁.r9,
      by rw [State.withRegions_gpr, g₂ _ (by decide) (by decide)]; exact a₁.r10,
      by rw [State.withRegions_gpr, g₂ _ (by decide) (by decide)]; exact a₁.h2,
      by simp only [hval, State.withRegions_gpr, g₂ _ (show Reg.r11 ≠ .rax by decide) (by decide),
        g₂ _ (show Reg.rbx ≠ .rax by decide) (by decide), g₂ _ (show Reg.rbp ≠ .rax by decide) (by decide)]
         exact a₁.val⟩
  · rw [State.withRegions_mem, ← hm]
    refine FA.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨⟨dp + BitVec.ofNat 64 448, L - 448⟩, by simp, wsub'⟩
    · exact ⟨stR (stA c), by simp, fun _ h => h⟩
    · exact ⟨⟨slot (bfA c), 8⟩, by simp, fun _ h => h⟩

/-- The key and the accumulator `enter` loads, from a Poly1305 state that
represents `msg`. -/
theorem enter_acc {c : Addr} {s s₁ : State} {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg)
    (r8₁ : s₁.gpr .r8 = s.mem.readW (off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0)
    (r9₁ : s₁.gpr .r9 = s.mem.readW (off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1)
    (r10₁ : (s₁.gpr .r10).toNat = 5 * ((s₁.gpr .r9).toNat / 4))
    (r11₁ : s₁.gpr .r11 = s.mem.readW (off (psA c) 0) 64) (rbx₁ : s₁.gpr .rbx = s.mem.readW (off (psA c) 8) 64)
    (rbp₁ : s₁.gpr .rbp = s.mem.readW (off (psA c) 16) 64) :
    ∃ R0 R1 A, Key R0 R1 ∧ clamp (leNum (key.take 16)) = rN R0 R1 ∧ A = accumulate (rN R0 R1) msg ∧
      Acc R0 R1 A s₁ := by
  obtain ⟨R0, hR0⟩ : ∃ R0, s.mem.readW (off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 = R0 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, s.mem.readW (off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 = R1 := ⟨_, rfl⟩
  have hk : Key R0 R1 := ⟨hR0 ▸ Proof.Poly1305.X86_64.r0_lt _, hR1 ▸ Proof.Poly1305.X86_64.r1_lt _,
    hR1 ▸ Proof.Poly1305.X86_64.r1_mod _⟩
  have hr : clamp (leNum (key.take 16)) = rN R0 R1 := by
    rw [← hrep.2.1, ← Proof.Poly1305.X86_64.off_24, Proof.Poly1305.X86_64.clamp_key, hR0, hR1]
  obtain ⟨A, hA⟩ : ∃ A, leNum (bytesAt s.mem (psA c) 24) = A := ⟨_, rfl⟩
  have hAm : A = accumulate (rN R0 R1) msg := by rw [← hA, hrep.2.2, hr]
  have hAP : A < P := hAm ▸ VG.Proof.Poly1305.accumulate_lt _ _
  rw [Proof.Poly1305.X86_64.leNum_acc] at hA
  refine ⟨R0, R1, A, hk, hr, hAm, r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
  · have hP : P = 2 ^ 130 - 5 := rfl
    rw [rbp₁]; omega_using [hA, hAP, hP]
  · simp only [hval, r11₁, rbx₁, rbp₁, hA]

/-- The bytes `cryptS` absorbs of `L > 448` bytes when the prologue computed
the keystream of the first 448: all but the 1 to 448 after the last chunk. -/
abbrev aP (L : Nat) : Nat := 448 + 512 * ((L - 449) / 512)

/-- After `bulkP`, or `tailS` after the 448 bytes, from `s`: the data after
the 448 bytes encrypted from the counter in `s`, the 448 bytes kept, the
first `aP L` bytes of ciphertext absorbed, and nothing left to encrypt. -/
structure PreDone (c dp : Addr) (L : Nat) (s : State) (key msg : List Byte) (s' : State) : Prop where
  data : ∀ k < L - 448, s'.mem (dp + BitVec.ofNat 64 (448 + k)) =
    s.mem (dp + BitVec.ofNat 64 (448 + k)) ^^^ (keystream (stateAt s.mem (stA c)) (L - 448)).getD k 0
  pre : ∀ k < 448, s'.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k)
  repr : Repr s'.mem (psA c) key (msg ++ bytesAt s'.mem dp (aP L))
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (aP L)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L - aP L)
  rdx : s'.gpr .rdx = 0
  rcx : s'.gpr .rcx = bfA c
  r12 : s'.gpr .r12 = s.gpr .r12
  r13 : s'.gpr .r13 = s.gpr .r13
  r14 : s'.gpr .r14 = s.gpr .r14
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The 448 bytes: apart from the context. -/
theorem pre_ctx {c dp : Addr} {L : Nat} (hl : Lay c dp L) (h448 : 448 ≤ L) {k : Nat} (hk : k < 448) {d n : Nat}
    (hd : d + n ≤ 1248) : ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := fun hc =>
  hl.cd hd _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by have := hl.L_lt; omega_arith) (by have := hl.L_lt; omega_arith))

/-- The 448 bytes: apart from the data after them. -/
theorem pre_after {dp : Addr} {L : Nat} (hL : L < 2 ^ 64) (hnw : dp.toNat + L ≤ 2 ^ 64) (h448 : 448 ≤ L) {k : Nat}
    (hk : k < 448) {o n : Nat} (ho : 448 ≤ o) (hon : o + n ≤ L) :
    ¬ (⟨dp + BitVec.ofNat 64 o, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
  split <;> omega_arith

theorem bulkP_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 960 ≤ L)
    (hr : 1 ≤ (L - 448) % 512 ∧ (L - 448) % 512 ≤ 448) {s : State} (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 448)) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (bulkP vl) s (PreDone c dp L s key msg) := by
  have hLe := hl.L_lt
  have hnw := hl.nowrap
  have hl' := hl.shift (o := 448) (by omega_arith)
  unfold bulkP
  refine WP.seq (WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_)
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr'
    rcases hr' with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, R1, A, hk, hcl, hAm, acc₁⟩ := enter_acc hrep r8₁ r9₁ r10₁ r11₁ rbx₁ rbp₁
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst
  have P₁ : bytesAt s₁.mem dp 448 = bytesAt s.mem dp 448 := by
    simp only [bytesAt]
    exact List.map_congr_left fun k hk => enter_data hl F₁ k (by rw [List.mem_range] at hk; omega_arith)
  refine WP.seq (WP.mono (chunkP_ok vl hl hk (m₀ := s₁.mem) (sp := s.gpr .rsp) hge (by rw [wr₁, hwr]) rdi₁
    (by rw [gk _ (.inl rfl), hrcx]) (by rw [gk _ (.inr (.inl rfl)), hrsi]) (gk _ (.inr (.inr rfl)))
    (by rw [sl₁, hrdx]) rfl C₁ acc₁) fun s₂ ⟨L₂, cf₂, rd₂, wr₂, F₂⟩ => ?_)
  -- The rest, on the permissions of the data after the 448 bytes.
  have hcov : Covers (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448)) s₂.wr := by
    rw [wr₂, wr₁, hwr]
    refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨stR (stA c), by simp, 0, by simp, by simp⟩
    · exact ⟨⟨dp, L⟩, by simp, 448, rfl, by show 448 + (L - 448) ≤ L; omega_arith⟩
    · exact ⟨bufR (bfA c), by simp, 0, by simp, by simp⟩
    · exact ⟨psR c, by simp, 0, by simp, by simp⟩
    · exact ⟨kR (bfA c), by simp, 0, by simp, by simp⟩
  have hn : ((.seq (.ite .b (.block []) (.loop (chunk vl false) .ae)) (restT vl) : Prog isa)).noCalls = true := by
    cases vl <;>
    decide +kernel
  have hlen : (msg ++ bytesAt s.mem dp 448).length % 16 = 0 := by
    rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hrep.1; omega_arith
  refine regionModel.wp_narrow (r := []) (w := bulkWr c (dp + BitVec.ofNat 64 448) (L - 448))
    (restLI_ok vl hl' hk (σ := s.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448)))
      (key := key) (msg := msg ++ bytesAt s.mem dp 448) rfl rfl hlen hrep.2.1 hcl
      (by rw [hAm, VG.Proof.Poly1305.accumulate_append hrep.1, P₁])
      (by rw [State.withRegions_mem, S₁]) (fun k hk => by
        rw [State.withRegions_mem]; exact enter_data hl' F₁ k hk)
      (by rw [State.withRegions_mem]; exact enter_key F₁) v12 v13 v14 L₂ cf₂)
    (Covers.right hcov) hcov (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
  have f₃' : Frame (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448)) s₂.mem s₃.mem := f₃
  -- The 448 bytes are kept.
  have hpre : ∀ k < 448, s₃.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k) := by
    intro k hk
    rw [f₃' _ (by
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl
        · exact pre_ctx hl (by omega_arith) hk (by decide)
        · exact pre_after hLe hnw (by omega_arith) hk (Nat.le_refl _) (by omega_arith)
        · exact pre_ctx hl (by omega_arith) hk (by decide)
        · exact pre_ctx hl (by omega_arith) hk (by decide)
        · rw [show kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ by simp only [kR, kA, bfA, Offset.add_add]]
          exact pre_ctx hl (by omega_arith) hk (by decide)),
      F₂ _ (by
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl
        · exact fun hc => pre_ctx hl (by omega_arith) hk (d := 128) (n := 320) (by decide) (slotsR_sub _ _ hc)
        · exact pre_after hLe hnw (by omega_arith) hk (Nat.le_refl _) (by omega_arith)
        · exact pre_ctx hl (by omega_arith) hk (by decide)
        · rw [slot_eq]; exact pre_ctx hl (by omega_arith) hk (by decide)),
      enter_data hl F₁ k (by omega_arith)]
  obtain ⟨T, ⟨t1, le, lt, hx, -⟩ | ⟨t1, le, lo, hi, data, repr, rbx, rbp, rdx, rcx, r12, r13, r14, r15, rsp, -, -⟩⟩ := hP
  · exfalso
    have : L - 448 - 512 * T = (L - 448) % 512 := by omega_arith
    omega_arith
  have hT : (L - 449) / 512 = T := by omega_arith
  have ea : aP L = 448 + 512 * T := by rw [aP, hT]
  have rbp' : s₃.gpr .rbp = BitVec.ofNat 64 (L - 448 - 512 * T) := rbp
  have rd₃' : s₃.rd = s₂.rd := rd₃
  have wr₃' : s₃.wr = s₂.wr := wr₃
  have data' : ∀ k < L - 448, s₃.mem (dp + BitVec.ofNat 64 448 + BitVec.ofNat 64 k) =
      s.mem (dp + BitVec.ofNat 64 448 + BitVec.ofNat 64 k) ^^^
        (keystream (stateAt s.mem (stA c)) (L - 448)).getD k 0 := data
  have repr' : Repr s₃.mem (psA c) key (msg ++ bytesAt s.mem dp 448 ++
      bytesAt s₃.mem (dp + BitVec.ofNat 64 448) (512 * T)) := repr
  refine ⟨fun k hk => ?_, hpre, ?_, by rw [ea, ← Offset.add_add]; exact rbx,
    by rw [ea, rbp', show L - 448 - 512 * T = L - (448 + 512 * T) by omega_arith],
    rdx, rcx, r12, r13, r14, r15, rsp, by rw [rd₃', rd₂, rd₁], by rw [wr₃', wr₂, wr₁]⟩
  · rw [← Offset.add_add, data' k hk]
  · rw [ea, VG.Proof.Poly1305.bytesAt_add, ← List.append_assoc]
    have hb : bytesAt s₃.mem dp 448 = bytesAt s.mem dp 448 := by
      simp only [bytesAt]
      exact List.map_congr_left fun k hk => hpre k (by rw [List.mem_range] at hk; exact hk)
    rw [hb]; exact repr'

/-- `TP` reads no flag, of the registers only the kernel's, `rsi` and
Poly1305's key and accumulator, and of the memory only its slot: `rdx`
written keeps it. -/
theorem TP.of_rdx {c dp : Addr} {L o N n : Nat} {R0 R1 : BitVec 64} {X : Nat} {sp : Addr} {s s' : State}
    (h : TP c dp L o N n R0 R1 X sp s) (hg : ∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hw : s'.wr = s.wr) : TP c dp L o N n R0 R1 X sp s' :=
  ⟨by rw [hw]; exact h.st, by rw [hw]; exact h.bf, by rw [hw]; exact h.ps, by rw [hw]; exact h.dw, h.le,
    by rw [hg _ (by decide)]; exact h.rdi, by rw [hg _ (by decide)]; exact h.rcx,
    by rw [hg _ (by decide)]; exact h.rsi, by rw [hg _ (by decide)]; exact h.rsp, by rw [hm]; exact h.left,
    ⟨by rw [hg _ (by decide)]; exact h.acc.r8, by rw [hg _ (by decide)]; exact h.acc.r9,
      by rw [hg _ (by decide)]; exact h.acc.r10, by rw [hg _ (by decide)]; exact h.acc.h2,
      by simp only [hval, hg Reg.r11 (by decide), hg Reg.rbx (by decide), hg Reg.rbp (by decide)]
         exact h.acc.val⟩⟩

/-- The bytes left read from the slot, less one, compared with 256. -/
theorem lenP_ok {c dp : Addr} {L o N n : Nat} {R0 R1 : BitVec 64} {X : Nat} {sp : Addr}
    (hL : L < 2 ^ 64) {s : State} (h : TP c dp L o N n R0 R1 X sp s) :
    WP isa (.block [.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 1), .alu .cmp .rdx (.imm 256)]) s
      fun s' => TP c dp L o N n R0 R1 X sp s' ∧ s'.mem = s.mem ∧ s'.wr = s.wr ∧ s'.rd = s.rd ∧
        (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧
        s'.cf = some (decide (1 ≤ n ∧ n ≤ 256)) ∧ s'.gpr .rdx = BitVec.ofNat 64 n - 1 := by
  have hn := h.le
  have hsl : InRegions (s.rd ++ s.wr) (slot (bfA c)) 8 := ⟨psR c, List.mem_append_right _ h.ps, slot_in⟩
  have hv := h.left
  simp only [slot, lenOff] at hsl hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, readSrc, execAlu,
    arithFlags, State.load64, State.setReg, State.setFlags, lenOff, h.rcx, hsl, hv, ite_true, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  have hg : ∀ r, r ≠ .rdx → (fun r' => if r' = .rdx then BitVec.ofNat 64 n - 1 else s.gpr r') r = s.gpr r :=
    fun r hr => by simp [hr]
  refine ⟨TP.of_rdx h (fun r hr => by simp [hr]) rfl rfl, trivial, trivial, trivial, fun r hr => by simp [hr], ?_, by simp⟩
  rw [e1, e256, Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide)]
  congr 1
  apply propext
  rw [BitVec.toNat_sub, Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega), show (1 : BitVec 64).toNat = 1 from rfl]
  constructor
  · intro hc
    by_cases h0 : n = 0
    · rw [h0] at hc; simp at hc
    · rw [show 2 ^ 64 - 1 + n = 2 ^ 64 + (n - 1) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)] at hc
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - 1 + n = 2 ^ 64 + (n - 1) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- With 1 to 256 bytes left (`rdx` one less), the comparison with 128. -/
theorem cmpP128_ok {n : Nat} (hlo : 1 ≤ n) (hhi : n ≤ 256) {s : State} (hrdx : s.gpr .rdx = BitVec.ofNat 64 n - 1) :
    WP isa (.block [.alu .cmp .rdx (.imm 128)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.wr = s.wr ∧ s'.rd = s.rd ∧ s'.cf = some (decide (n ≤ 128)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  rw [hrdx, e128, Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide),
    show BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)],
    Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega)]
  congr 1
  apply propext
  constructor <;> intro <;> omega

/-- No whole chunks after the 448 bytes: the rest (1 to 512 bytes) encrypted
while the 448 bytes are absorbed, by `tailS` with one set of blocks (up to
128 bytes) or two (up to 256), or by `tailKX` (up to 512). -/
theorem tailPS_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hlo : 449 ≤ L) (hhi : L ≤ 960)
    {s : State} (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 448)) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (.seq (.block enter) (tailP vl)) s (PreDone c dp L s key msg) := by
  have hLe := hl.L_lt
  have hnw := hl.nowrap
  refine WP.seq (WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_)
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr'
    rcases hr' with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, R1, A, hk, hcl, hAm, acc₁⟩ := enter_acc hrep r8₁ r9₁ r10₁ r11₁ rbx₁ rbp₁
  have hAP : A < P := hAm ▸ VG.Proof.Poly1305.accumulate_lt _ _
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst
  have z : dp + BitVec.ofNat 64 0 = dp := by simp
  have tp : TP c dp L 0 448 (L - 448) R0 R1 A (s.gpr .rsp) s₁ :=
    ⟨by rw [wr₁, hwr]; simp, by rw [wr₁, hwr]; simp, by rw [wr₁, hwr]; simp, by rw [wr₁, hwr]; simp, by omega_arith,
      rdi₁, by rw [gk _ (.inl rfl), hrcx], by rw [gk _ (.inr (.inl rfl)), hrsi, z], gk _ (.inr (.inr rfl)),
      by rw [sl₁, hrdx], acc₁⟩
  have ea : aP L = 448 := by simp only [aP]; omega_arith
  -- What any of the three tails leaves.
  have fin : ∀ {t s₂ : State}, t.mem = s₁.mem → t.rd = s₁.rd → t.wr = s₁.wr →
      ((∀ k < L - 448, s₂.mem (dp + BitVec.ofNat 64 (0 + 448) + BitVec.ofNat 64 k) =
        t.mem (dp + BitVec.ofNat 64 (0 + 448) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt t.mem (stA c)) (L - 448)).getD k 0) ∧
      leNum (bytesAt s₂.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt t.mem (dp + BitVec.ofNat 64 0) 448) % P ∧
      Frame [accR c, bufR (bfA c), kR (bfA c), ⟨dp + BitVec.ofNat 64 (0 + 448), L - 448⟩] t.mem s₂.mem ∧
      s₂.gpr .rbx = dp + BitVec.ofNat 64 (0 + 448) ∧ s₂.gpr .rbp = BitVec.ofNat 64 (L - 448) ∧
      s₂.gpr .rdx = 0 ∧ s₂.gpr .rcx = bfA c ∧
      s₂.gpr .r12 = t.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s₂.gpr .r13 = t.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s₂.gpr .r14 = t.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s₂.gpr .r15 = c ∧
      s₂.gpr .rsp = s.gpr .rsp ∧ s₂.rd = t.rd ∧ s₂.wr = t.wr) → PreDone c dp L s key msg s₂ := by
    intro t s₂ mt rdt wrt ⟨d₂, acc₂, f₂, rbx₂, rbp₂, rdx₂, rcx₂, r12₂, r13₂, r14₂, r15₂, rsp₂, rd₂, wr₂⟩
    rw [mt] at d₂ acc₂ f₂ r12₂ r13₂ r14₂
    have hpre : ∀ k < 448, s₂.mem (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k) := by
      intro k hk
      rw [f₂ _ (by
          intro r hr'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
          rcases hr' with rfl | rfl | rfl | rfl
          · exact pre_ctx hl (by omega_arith) hk (by decide)
          · exact pre_ctx hl (by omega_arith) hk (by decide)
          · rw [show kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ by simp only [kR, kA, bfA, Offset.add_add]]
            exact pre_ctx hl (by omega_arith) hk (by decide)
          · exact pre_after hLe hnw (by omega_arith) hk (by omega_arith) (by omega_arith)),
        enter_data hl F₁ k (by omega_arith)]
    have hb : bytesAt s₂.mem dp 448 = bytesAt s₁.mem dp 448 := by
      simp only [bytesAt]
      exact List.map_congr_left fun k hk => by
        rw [List.mem_range] at hk; rw [hpre k hk, enter_data hl F₁ k (by omega_arith)]
    refine ⟨fun k hk => ?_, hpre, ⟨?_, ?_, ?_⟩, by rw [ea, rbx₂], by rw [ea, rbp₂], rdx₂, rcx₂,
      by rw [r12₂, v12], by rw [r13₂, v13], by rw [r14₂, v14], r15₂, by rw [rsp₂], by rw [rd₂, rdt, rd₁],
      by rw [wr₂, wrt, wr₁]⟩
    · have x := d₂ k hk
      rw [Offset.add_add, Nat.zero_add, enter_data hl F₁ _ (by omega_arith), S₁] at x
      exact x
    · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt, ea]; have := hrep.1; omega_arith
    · rw [psA_24]
      have e := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) f₂ (by
        intro r hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl
        · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
        · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
        · rw [show kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ by simp only [kR, kA, bfA, Offset.add_add]]
          exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
        · exact (hl.cd (by decide)).sub_right (Offset.sub_base _ (by omega_arith))) (by decide)
      rw [e, enter_key F₁, ← psA_24]; exact hrep.2.1
    · rw [acc₂, z, ea, hb, hcl, VG.Proof.Poly1305.accumulate_append hrep.1, ← hAm,
        Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt hAP _)]
  unfold tailP
  refine WP.seq (WP.mono (lenP_ok hLe tp) fun s₃ ⟨tp₃, m₃, w₃, rd₃, g₃, c₃, d₃⟩ => ?_)
  refine WP.ite (decide (1 ≤ L - 448 ∧ L - 448 ≤ 256)) (by simp [eval, c₃]) (fun hc => ?_) (fun hc => ?_)
  · simp only [decide_eq_true_eq] at hc
    refine WP.seq (WP.mono (cmpP128_ok hc.1 hc.2 d₃) fun s₄ ⟨g₄, m₄, w₄, rd₄, c₄⟩ => ?_)
    have tp₄ : TP c dp L 0 448 (L - 448) R0 R1 A (s.gpr .rsp) s₄ :=
      TP.of_rdx tp₃ (fun r _ => by rw [g₄]) m₄ w₄
    have m₄' : s₄.mem = s₁.mem := by rw [m₄, m₃]
    have rd₄' : s₄.rd = s₁.rd := by rw [rd₄, rd₃]
    have w₄' : s₄.wr = s₁.wr := by rw [w₄, w₃]
    refine WP.ite (decide (L - 448 ≤ 128)) (by simp [eval, c₄]) (fun hc' => ?_) (fun hc' => ?_)
    · simp only [decide_eq_true_eq] at hc'
      refine WP.mono (tailSg_ok hl hk false true (o := 0) (N := 448) (n := L - 448) rfl (by omega_arith)
        (by simp only [Bool.false_eq_true, ite_false]; omega_arith) tp₄) fun s₂ ⟨d, a, f, rest⟩ => ?_
      exact fin m₄' rd₄' w₄' ⟨d, a, f.mono (by simp), rest⟩
    · simp only [decide_eq_false_iff_not] at hc'
      refine WP.mono (tailSg_ok hl hk true true (o := 0) (N := 448) (n := L - 448) rfl (by omega_arith)
        (by simp only [ite_true]; omega_arith) tp₄) fun s₂ ⟨d, a, f, rest⟩ => ?_
      exact fin m₄' rd₄' w₄' ⟨d, a, f.mono (by simp), rest⟩
  · simp only [decide_eq_false_iff_not] at hc
    refine WP.mono (tailKXg_ok vl true hl hk (o := 0) (N := 448) (n := L - 448) rfl (by omega_arith)
      (by omega_arith) (by omega_arith) tp₃ (by rw [m₃]; exact C₁) (by rw [w₃, wr₁, hwr]; simp))
      fun s₂ h₂ => fin m₃ rd₃ w₃ h₂

/-! ## What the constant-time proof needs -/

/-- `bulkP`'s `enter` and first chunk: after `enter`, the kernel's pointers;
after the first chunk, the loop invariant on the data after the 448 bytes,
from whose narrowed state the rest runs. -/
theorem bulkPHead_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 960 ≤ L) {s : State}
    (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 448)) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (.block enter) s fun s₁ => s₁.gpr .rdi = stA c ∧ s₁.gpr .rcx = bfA c ∧ s₁.gpr .rsi = dp ∧
      s₁.gpr .rsp = s.gpr .rsp ∧
      WP isa (chunk vl true) s₁ fun s₂ =>
        (∃ R0 R1 A m₀, Key R0 R1 ∧ LI c (dp + BitVec.ofNat 64 448) (L - 448) R0 R1 A m₀ (s.gpr .rsp) 1
          (s₂.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448)))) ∧
        s₂.cf = some (decide (L - 448 - 512 * 1 < 512)) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧
        ∃ F, WP isa (.seq (.ite .b (.block []) (.loop (chunk vl false) .ae)) (restT vl))
          (s₂.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448))) F := by
  have hl' := hl.shift (o := 448) (by omega_arith)
  refine WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr'
    rcases hr' with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, R1, A, hk, hcl, hAm, acc₁⟩ := enter_acc hrep r8₁ r9₁ r10₁ r11₁ rbx₁ rbp₁
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have S₁ : stateAt s₁.mem (stA c) = stateAt s.mem (stA c) := Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst
  have P₁ : bytesAt s₁.mem dp 448 = bytesAt s.mem dp 448 := by
    simp only [bytesAt]
    exact List.map_congr_left fun k hk => enter_data hl F₁ k (by rw [List.mem_range] at hk; omega_arith)
  have hlen : (msg ++ bytesAt s.mem dp 448).length % 16 = 0 := by
    rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hrep.1; omega_arith
  refine ⟨rdi₁, by rw [gk _ (.inl rfl), hrcx], by rw [gk _ (.inr (.inl rfl)), hrsi], gk _ (.inr (.inr rfl)),
    WP.mono (chunkP_ok vl hl hk (m₀ := s₁.mem) (sp := s.gpr .rsp) hge (by rw [wr₁, hwr]) rdi₁
      (by rw [gk _ (.inl rfl), hrcx]) (by rw [gk _ (.inr (.inl rfl)), hrsi]) (gk _ (.inr (.inr rfl)))
      (by rw [sl₁, hrdx]) rfl C₁ acc₁) fun s₂ ⟨L₂, cf₂, rd₂, wr₂, _⟩ =>
    ⟨⟨R0, R1, _, _, hk, L₂⟩, cf₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], _,
      restLI_ok vl hl' hk (σ := s.withRegions [] (bulkWr c (dp + BitVec.ofNat 64 448) (L - 448)))
        (key := key) (msg := msg ++ bytesAt s.mem dp 448) rfl rfl hlen hrep.2.1 hcl
        (by rw [hAm, VG.Proof.Poly1305.accumulate_append hrep.1, P₁])
        (by rw [State.withRegions_mem, S₁]) (fun k hk => by
          rw [State.withRegions_mem]; exact enter_data hl' F₁ k hk)
        (by rw [State.withRegions_mem]; exact enter_key F₁) v12 v13 v14 L₂ cf₂⟩⟩

/-- `enter` before the tail after the 448 bytes: what `tailS` and `tailKX` need. -/
theorem enterTP_ok {c dp : Addr} {L : Nat} (hlo : 449 ≤ L) {s : State}
    (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 448)) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (.block enter) s fun s₁ => ∃ R0 R1 X, Key R0 R1 ∧ TP c dp L 0 448 (L - 448) R0 R1 X (s.gpr .rsp) s₁ ∧
      Consts s₁.mem (bfA c) ∧ kR (bfA c) ∈ s₁.wr := by
  refine WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr'
    rcases hr' with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨R0, R1, A, hk, -, -, acc₁⟩ := enter_acc hrep r8₁ r9₁ r10₁ r11₁ rbx₁ rbp₁
  exact ⟨R0, R1, A, hk, ⟨by rw [wr₁, hwr]; simp, by rw [wr₁, hwr]; simp, by rw [wr₁, hwr]; simp,
    by rw [wr₁, hwr]; simp, by omega_arith, rdi₁, by rw [gk _ (.inl rfl), hrcx],
    by rw [gk _ (.inr (.inl rfl)), hrsi]; simp, gk _ (.inr (.inr rfl)), by rw [sl₁, hrdx], acc₁⟩, C₁,
    by rw [wr₁, hwr]; simp⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
