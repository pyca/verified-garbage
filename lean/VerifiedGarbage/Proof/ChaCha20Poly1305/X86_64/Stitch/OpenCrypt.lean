import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.OpenBulk
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified

/-!
# ChaCha20 and Poly1305 together (x86-64): `cryptO`

`Stitch.cryptO`, in `open`'s context, does what `open`'s `macPadLengths`
followed by `crypt` does (`cryptO_ok`): the padded ciphertext and the
lengths block absorbed, and the data decrypted. With at most `fold` bytes it
is that code. Otherwise `bulkO` decrypts and absorbs the whole chunks
(`bulkO_ok`, moved to `open`'s permissions with `RegionModel.wp_narrow`),
or nothing below 512 bytes (`MidO`); `macPadLengths` absorbs the rest, as it
was on entry, and the lengths block; and `vg_chacha20_xor` decrypts the
rest from the counter `bulkO` leaves.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt keystream initState)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-- After `cryptO`'s branch on 512 bytes: the first `E` bytes (a multiple of
64, all the whole chunks) decrypted, and their ciphertext, as it was in the
state `s` before the branch's arguments, absorbed. -/
structure MidO (s₀ s : State) (key msg : List Byte) (E : Nat) (s' : State) : Prop where
  rbx : s'.gpr .rbx = dp s₀ + BitVec.ofNat 64 E
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L s₀ - E)
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  E64 : E % 64 = 0
  EL : E ≤ L s₀
  st : stateAt s'.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64)
  data : ∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then
    s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 512, dR s₀] s.mem s'.mem
  repr : Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) E)

/-- Below 512 bytes: nothing decrypted yet, nothing absorbed. -/
theorem whole_midO {s₀ : State} (hp : APre e s₀) {s s₂ : State} (ha : Args s₀ s s₂)
    (h15 : s₂.gpr .r15 = s.gpr .r15)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.block whole) s₂ (MidO s₀ s key msg 0) := by
  refine WP.mono (whole_ok s₂) fun s₃ ⟨rbx₃, rbp₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  refine ⟨by rw [rbx₃, ha.r14]; simp, by rw [rbp₃, ha.r13, Nat.sub_zero], fun r hr => ?_, by rw [rd₃, ha.rd],
    by rw [wr₃, ha.wr], rfl, Nat.zero_le _, ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inl rfl)]
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inr (.inl rfl))]
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inr (.inr (.inl rfl)))]
    · rw [g₃ _ (by decide) (by decide), h15]
    · rw [g₃ _ (by decide) (by decide), ha.keep _ (.inr (.inr (.inr rfl)))]
  · rw [m₃, ha.mem, stateAt_ctr, hst, set12_initState, Nat.zero_div, VG.Proof.ChaCha20.ctr_zero]
  · rw [m₃, ha.mem, args_data hp _ hk, ite_eq_right (Nat.not_lt_zero _)]
  · rw [m₃, ha.mem]
    exact (args_frame s₀ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · rw [show bytesAt s.mem (dp s₀) 0 = [] from rfl, List.append_nil, m₃, ha.mem]
    exact args_repr hrep

/-- The whole chunks: `bulkO`, with its permissions. -/
theorem bulk_midO {s₀ : State} (hp : APre e s₀) {s s₂ : State} (hwr : s.wr = s₀.wr) (ha : Args s₀ s s₂)
    (h15 : s.gpr .r15 = cx s₀) (hge : 512 ≤ L s₀)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa bulkO s₂ fun s₃ => ∃ E, MidO s₀ s key msg E s₃ := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hl : Lay (cx s₀) (dp s₀) (L s₀) := ⟨hL9, hp.wrap_d, hp.c_d.sub_left (Region.sub_prefix (by decide))⟩
  have st₂ : stateAt s₂.mem (stA (cx s₀)) = initState (K s₀) 1 (N s₀) := by
    show stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64) = _
    rw [ha.mem, ← off_eq, stateAt_ctr, hst, set12_initState]
  have hw : Covers (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.wr := bulk_covers hp (by rw [ha.wr, hwr])
  have hn : bulkO.noCalls = true := by decide +kernel
  refine regionModel.wp_narrow (r := []) (w := bulkWr (cx s₀) (dp s₀) (L s₀))
    (bulkO_ok hl hge (s := s₂.withRegions [] (bulkWr (cx s₀) (dp s₀) (L s₀))) rfl rfl ha.rsi ha.rdx
      (by rw [State.withRegions_gpr, ha.rcx, off_eq])
      (by show Repr _ (cx s₀ + BitVec.ofNat 64 448) _ _
          rw [State.withRegions_mem, ha.mem, ← off_eq]; exact args_repr hrep))
    (Covers.right hw) hw (Code.noFrames_of_noCalls hn) (.inl hn) fun _ s₃ _ rd₃ wr₃ f₃ hP => ?_
  obtain ⟨T, t1, le, lt, data, cnt, repr, rbx, rbp, rsi, rdx, rdi, rcx, r12, r13, r14, r15, rsp, -, -⟩ := hP
  have f₃' : Frame (bulkWr (cx s₀) (dp s₀) (L s₀)) s₂.mem s₃.mem := f₃
  have cnt' : stateAt s₃.mem (cx s₀ + BitVec.ofNat 64 64) =
      ctr (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (8 * T) := cnt
  have data' : ∀ k < L s₀, s₃.mem (dp s₀ + BitVec.ofNat 64 k) = if k < 512 * T then
      s₂.mem (dp s₀ + BitVec.ofNat 64 k) ^^^
        (keystream (stateAt s₂.mem (cx s₀ + BitVec.ofNat 64 64)) (L s₀)).getD k 0
      else s₂.mem (dp s₀ + BitVec.ofNat 64 k) := data
  have hb : bytesAt s₂.mem (dp s₀) (512 * T) = bytesAt s.mem (dp s₀) (512 * T) := by
    simp only [bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [ha.mem, args_data hp _ (by have := List.mem_range.mp hk; omega)]
  refine ⟨512 * T, rbx, rbp, fun r hr => ?_, (rd₃ : s₃.rd = s₂.rd).trans ha.rd, (wr₃ : s₃.wr = s₂.wr).trans ha.wr,
    by omega, le, ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (r12 : s₃.gpr .r12 = s₂.gpr .r12).trans (ha.keep _ (.inl rfl))
    · exact (r13 : s₃.gpr .r13 = s₂.gpr .r13).trans (ha.keep _ (.inr (.inl rfl)))
    · exact (r14 : s₃.gpr .r14 = s₂.gpr .r14).trans (ha.keep _ (.inr (.inr (.inl rfl))))
    · exact (r15 : s₃.gpr .r15 = cx s₀).trans h15.symm
    · exact (rsp : s₃.gpr .rsp = s₂.gpr .rsp).trans (ha.keep _ (.inr (.inr (.inr rfl))))
  · rw [off_eq, cnt', st₂, show 512 * T / 64 = 8 * T by omega]
  · rw [data' k hk, st₂, ha.mem, args_data hp _ hk]
  · rw [ha.mem] at f₃'
    refine ((args_frame s₀ s.mem).sub fun r hr => ?_).trans (f₃'.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 512, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have e : sub s₀ 64 512 = ⟨cx s₀ + BitVec.ofNat 64 64, 512⟩ := by rw [sub, off_eq]
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨sub s₀ 64 512, by simp, by rw [e]; exact Offset.sub _ (by decide) (by decide)⟩
  · rw [off_eq, ← hb]; exact repr

theorem movRest_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .rbx), .mov .rdx (.reg .rbp)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rbx ∧ s'.gpr .rdx = s.gpr .rbp ∧ (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left',
    reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

/-- `restArgs`: the arguments of the call on the rest. -/
theorem restArgs_ok {s₀ : State} {s : State} (h15 : s.gpr .r15 = cx s₀) :
    WP isa (.block restArgs) s fun s' =>
      s'.gpr .rdi = off (cx s₀) 64 ∧ s'.gpr .rsi = s.gpr .rbx ∧ s'.gpr .rdx = s.gpr .rbp ∧
      s'.gpr .rcx = off (cx s₀) 128 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  unfold restArgs
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 64) (by lit_omega) s)
    fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (movRest_ok s₁) fun s₂ ⟨rsi₂, rdx₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  refine WP.mono (ptr_ok .rcx .r15 (k := 128) (by lit_omega) s₂) fun s₃ ⟨e₃, g₃, rd₃, wr₃, m₃⟩ => ?_
  refine ⟨by rw [g₃ _ (by decide), g₂ _ (by decide) (by decide), e₁, h15],
    by rw [g₃ _ (by decide), rsi₂, g₁ _ (by decide)], by rw [g₃ _ (by decide), rdx₂, g₁ _ (by decide)],
    by rw [e₃, g₂ _ (by decide) (by decide), g₁ _ (by decide), h15], fun r a b c d => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, m₂, m₁]⟩
  rw [g₃ r d, g₂ r b c, g₁ r a]

/-- The rest, `[E, L)`, decrypted by the implementation `v` of `vg_chacha20_xor`
from the counter the chunks left. -/
theorem restCall_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) {E : Nat} (hE : E % 64 = 0) (hEL : E ≤ L s₀)
    (hrbx : s.gpr .rbx = dp s₀ + BitVec.ofNat 64 E) (hrbp : s.gpr .rbp = BitVec.ofNat 64 (L s₀ - E))
    (hst : stateAt s.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64)) :
    WP isa (.seq (.block restArgs) (.call v.callee.name v.callee.code)) s fun s' =>
      s'.gpr .rsi = off (cx s₀) 128 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
        else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0) ∧
      s'.mxcsr = s.mxcsr := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩ (dR s₀) := Offset.sub_base _ (by omega)
  refine WP.seq (WP.mono_mx (by decide +kernel) (restArgs_ok (s₀ := s₀) h.r15)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, rcx₁, g₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h.rsp]
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀ + BitVec.ofNat 64 E, L s₀ - E⟩, ⟨off (cx s₀) 128, 320⟩]
      s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁, h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega⟩
    · exact ⟨dR s₀, by rw [wr₁, h.wr]; exact hp.d_wr, E, rfl, by show E + (L s₀ - E) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, by rw [wr₁, h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega⟩
  refine WP.mono_mx (by simp only [Code.allInstrs, v.mxcsr]) (Q := fun s' => s'.gpr .rsi = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem ∧
      (∀ k < L s₀, s'.mem (dp s₀ + BitVec.ofNat 64 k) = if k < E then s.mem (dp s₀ + BitVec.ofNat 64 k)
        else s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0))
    ?_ fun s' h' mx' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2, by rw [mx', mx₁]⟩
  refine xor_call v (S := off (cx s₀) 64) (D := dp s₀ + BitVec.ofNat 64 E) (B := off (cx s₀) 128)
    rdi₁ (by rw [rsi₁, hrbx]) (by rw [rdx₁, hrbp]) rcx₁ (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right dsub)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left dsub)
    (Nat.le_trans (Nat.add_le_add_right (toNat_add_le _ E (by omega)) _) (by have := hp.wrap_d; omega))
    (by rw [rsp₁]; exact hp.stk_sub (by lit_omega)) (by rw [rsp₁]; exact hp.stk_d.sub_right dsub)
    (by rw [rsp₁]; exact hp.stk_sub (by lit_omega)) (Covers.right hw) hw
    fun s' rd' wr' cs' f' rsi' data' => ?_
  rw [rsp₁] at f'
  have ks' : (keystream (stateAt s₁.mem (off (cx s₀) 64)) (L s₀ - E)).length = L s₀ - E :=
    VG.Proof.ChaCha20.length_keystream _ _
  refine ⟨rsi', fun r hr => ?_, by rw [rd', rd₁], by rw [wr', wr₁], ?_, fun k hk => ?_⟩
  · have := calleeSaved_ne hr
    rw [cs' r hr, g₁ r this.2.2.2.2 this.2.2.2.1 this.2.2.1 this.2.1]
  · rw [m₁] at f'
    refine f'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, dsub⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · by_cases hkE : k < E
    · rw [ite_eq_left hkE, ← m₁]
      refine f' _ fun r hr hc => ?_
      have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.c_d _ (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega) _ hc) hin
      · simp only [Region.Contains] at hc
        rw [Offset.sub_toNat' _ (by omega) (by omega)] at hc
        split at hc <;> omega
      · exact hp.c_d _ (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega) _ hc) hin
      · exact hp.stk_d _ hc hin
    · have x := xor_at ks' data' (j := k - E) (by omega)
      rw [Offset.add_add, Nat.add_sub_cancel' (by omega), m₁, hst, ks_from _ hE hk (by omega)] at x
      rw [ite_eq_right hkE, x]

/-- After `cryptO`'s branch, before the keystream is wiped: what `open`'s
`macPadLengths` and `crypt`'s branch leave. -/
structure CryptedO (s₀ s : State) (key msg : List Byte) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  keep : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .rsp → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 528, dR s₀, stkR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))
  repr : Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem (dp s₀) (L s₀) ++
    pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++ bytesAt s.mem (off (cx s₀) 592) 16)
  mx : s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

/-- More than `fold` bytes: the whole chunks decrypted and absorbed by
`bulkO` (none below 512 bytes), the rest and the lengths block absorbed, and
the rest decrypted by the implementation `v` of `vg_chacha20_xor`. -/
theorem bigO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.seq (.block (cryptArgs ++ [.alu .cmp .rdx (.imm 512)]))
      (.seq (.ite .b (.block whole) bulkO)
      (.seq (macPadLengths v.poly .rbx .rbp)
      (.seq (.block restArgs) (.call v.callee.name v.callee.code))))) s (CryptedO s₀ s key msg) := by
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (Q := fun (s₂ : State) => Args s₀ s s₂ ∧ s₂.gpr .r15 = s.gpr .r15 ∧ s₂.cf = some (decide (L s₀ < 512))) ?_
    fun s₂ ⟨ha, h15, cf₂⟩ mx₂ => ?_)
  · refine WP.block_append (WP.mono (cryptA_ok hp h) fun s₂ ⟨m₂, rdi₂, rsi₂, rdx₂, rcx₂, cs₂, rd₂, wr₂⟩ =>
      WP.mono (cmp512_ok hL9 (by rw [rdx₂, hL])) fun s₃ ⟨g₃, rd₃, wr₃, m₃, c₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun r hr => ?_, by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩, ?_, c₃⟩)
    · rw [m₃, m₂]
    · rw [g₃, rdi₂]
    · rw [g₃, rsi₂]
    · rw [g₃, rdx₂, hL]
    · rw [g₃, rcx₂]
    · rw [g₃, cs₂ _ (by simp [calleeSaved]), h.r13, hL]
    · rw [g₃, cs₂ _ (by simp [calleeSaved]), h.r14]
    · rw [g₃, cs₂ r (by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
    · rw [g₃, cs₂ _ (by simp [calleeSaved])]
  -- The whole chunks, if any.
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (Q := fun (s₃ : State) => ∃ E, MidO s₀ s key msg E s₃) ?_ fun s₃ ⟨E, hm⟩ mx₃ => ?_)
  · refine WP.ite (decide (L s₀ < 512)) (by simp [eval, cf₂]) (fun _ => ?_) (fun hc' => ?_)
    · exact WP.mono (whole_midO hp ha h15 hst hrep) fun s₄ hm₄ => ⟨0, hm₄⟩
    · simp only [decide_eq_false_iff_not] at hc'
      exact bulk_midO hp h.wr ha h.r15 (by omega) hst hrep
  have hEL := hm.EL
  have i₃ : Inv s₀ s₃ := Inv.step' h hm.keep hm.rd hm.wr hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))
  -- The rest absorbed, as it was on entry, with the lengths block.
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩
    (srcRest hp hEL) i₃ hm.rbx hm.rbp) fun s₄ ⟨i₄, cs₄, f₄, mx₄, r₄⟩ => ?_)
  have st₄ : stateAt s₄.mem (off (cx s₀) 64) = ctr (initState (K s₀) 1 (N s₀)) (E / 64) := by
    rw [stateAt_frame f₄ (by rdisj_all), hm.st]
  -- The rest decrypted.
  refine WP.mono (restCall_ok v hp i₄ hm.E64 hEL (by rw [cs₄ _ (by simp [calleeSaved]), hm.rbx])
    (by rw [cs₄ _ (by simp [calleeSaved]), hm.rbp]) st₄) fun s₅ ⟨rsi₅, cs₅, rd₅, wr₅, f₅, d₅, mx₅⟩ => ?_
  have dd : ∀ k < L s₀, ∀ r ∈ macR s₀, ¬ r.Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
    intro k hk r hr hc
    have hin : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.c_d _ (sub_ctx s₀ (k := 448) (n := 144) (by lit_omega) _ hc) hin
    · exact hp.stk_d _ hc hin
  have e₄ : ∀ k < L s₀, s₄.mem (dp s₀ + BitVec.ofNat 64 k) = s₃.mem (dp s₀ + BitVec.ofNat 64 k) :=
    fun k hk => f₄ _ (dd k hk)
  have rest : bytesAt s₃.mem (dp s₀ + BitVec.ofNat 64 E) (L s₀ - E) =
      bytesAt s.mem (dp s₀ + BitVec.ofNat 64 E) (L s₀ - E) := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [Offset.add_add, hm.data _ (by omega), ite_eq_right (by omega)]
  have lens : bytesAt s₃.mem (off (cx s₀) 592) 16 = bytesAt s.mem (off (cx s₀) 592) 16 :=
    bytesAt_frame hm.frame (by rdisj_all) (by lit_omega)
  refine ⟨rsi₅, fun r hr => ?_, by rw [rd₅, i₄.rd, h.rd], by rw [wr₅, i₄.wr, h.wr], ?_, ?_, ?_, ?_⟩
  · have hc : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [cs₅ r hc, cs₄ r hc, hm.keep r (by rcases hr with rfl | rfl | rfl | rfl <;> simp)]
  · refine ((hm.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
    · simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
    apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    rw [d₅ k hk, e₄ k hk]
    by_cases hkE : k < E
    · rw [ite_eq_left hkE, hm.data k hk, ite_eq_left hkE]
    · rw [ite_eq_right hkE, hm.data k hk, ite_eq_right hkE]
  · have R₄ := r₄ key _ hm.repr
    rw [rest, lens] at R₄
    have R₅ := Repr.frame f₅ (by rdisj_all) R₄
    rwa [List.append_assoc msg, split_pad _ _ (by have := hm.E64; omega) hEL] at R₅
  · rw [mx₅, mx₄, mx₃, mx₂]

/-- At most `fold` bytes: `open`'s `macPadLengths`, then the keystream from
the prologue XORed into them. -/
theorem smallO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hle : L s₀ ≤ v.callee.fold)
    (hks : ∀ k < mOf v.callee.fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (.seq (macPadLengths v.poly .r14 .r13)
      (.seq (.block (ptr .rsi .r15 736 ++ [.mov .rdx (.reg .r13)]))
        (.seq (xorBufX .r14) (.block (ptr .rsi .r15 128))))) s (CryptedO s₀ s key msg) := by
  have hL' := Nat.le_of_lt (s₀.gpr .r9).isLt
  have hM := Nat.le_trans (mOf_le v.callee.fold (L s₀)) v.fold_le
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) h
    h.r14 (by rw [h.r13]; exact hL s₀)) fun s₄ ⟨i₄, cs₄, f₄, mx₄, r₄⟩ => ?_)
  refine WP.mono_mx (by decide +kernel) (cryptSmall_ok v.fold_le hp i₄ hle (ks_frame f₄ (by rdisj_all) hM hks))
    fun s₅ c₅ mx₅ => ?_
  have D₄ : bytesAt s₄.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) := bytesAt_frame f₄ (by rdisj_all) hL'
  refine ⟨c₅.rsi, fun r hr => ?_, by rw [c₅.rd, i₄.rd, h.rd], by rw [c₅.wr, i₄.wr, h.wr], ?_, by rw [c₅.data, D₄],
    Repr.frame c₅.frame (by rdisj_all) (r₄ key msg hrep), by rw [mx₅, mx₄]⟩
  · have hc : r ∈ calleeSaved := by rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [c₅.cs r hc (by rcases hr with rfl | rfl | rfl | rfl <;> decide), cs₄ r hc]
  · refine (f₄.sub fun r hr => ?_).trans (c₅.frame.sub fun r hr => ?_)
    · simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sub s₀ 64 528, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- `cryptO`: as `open`'s `macPadLengths` and then `crypt`, by any
implementation `v` of `vg_chacha20_xor` and its `vg_poly1305_blocks`. -/
theorem cryptO_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mOf v.callee.fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0)
    {key msg : List Byte} (hrep : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptO v.callee v.poly) s fun s' => Inv s₀ s' ∧
      Frame [sub s₀ 64 528, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) ∧
      Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem (dp s₀) (L s₀) ++
        pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++ bytesAt s.mem (off (cx s₀) 592) 16) ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hfl := v.fold_le
  have hL9 : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hm := mOf_le v.callee.fold (L s₀)
  unfold cryptO
  refine WP.seq (WP.mono_mx rfl (cmpFold_ok (fold := v.callee.fold) (by lit_omega) h.r13)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ mx₁ => ?_)
  have h₁ : Inv s₀ s₁ := h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine WP.seq (WP.mono (Q := CryptedO s₀ s₁ key msg) ?_ fun s₂ c₂ => ?_)
  · refine WP.ite (decide (L s₀ < v.callee.fold + 1)) (by simp [eval, c₁]) (fun hc => ?_) (fun hc => ?_)
    · simp only [decide_eq_true_eq] at hc
      exact smallO_ok v hp h₁ (by omega) (by rw [m₁]; exact hks) (by rw [m₁]; exact hrep)
    · exact bigO_ok v hp h₁ (by rw [m₁]; exact hst) (by rw [m₁]; exact hrep)
  -- The keystream wiped, as in `crypt_ok`.
  refine WP.seq (WP.mono_mx (by decide +kernel) (anchor_ok .rsi (k := 128) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_)
  have cs₃ : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s₃.gpr r = s.gpr r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [g₃ _ (by decide), c₂.keep _ (.inl rfl), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inl rfl)), g₁]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inl rfl))), g₁]
    · rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ _ (by decide), c₂.keep _ (.inr (.inr (.inr rfl))), g₁]
  have fc : Frame [sub s₀ 64 528, dR s₀, stkR s₀] s.mem s₃.mem := by rw [m₃, ← m₁]; exact c₂.frame
  have i₃ : Inv s₀ s₃ := Inv.step' h cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁]) fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact stk_work s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
      · exact (hp.stk_sub (by lit_omega)).symm)
  refine WP.seq (WP.mono_mx rfl (foldM_ok (fold := v.callee.fold) (len := L s₀) (by lit_omega)
    hL9 (by rw [i₃.r13]; exact hL s₀)) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (add64_ok (n := mOf v.callee.fold (L s₀)) d₄)
    fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ mx₅ => ?_)
  refine WP.mono_mx (by decide +kernel) (zeroKs_ok hp (n := 64 + mOf v.callee.fold (L s₀)) (by omega)
    (by lit_omega) d₅ (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ mx₆ => ?_
  have g36 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by
    rw [g₆ r h1 h2, g₅ r h3, g₄ r h3]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  have hbd : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s₃.mem (dp s₀) (L s₀) :=
    bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (by omega)
  refine ⟨Inv.step' i₃ (fun r hr => g36 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    ?_, ?_, ?_, ?_⟩
  · refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [hbd, m₃, c₂.data, m₁]
  · rw [← m₁]
    refine Repr.frame f₅₆ (fun r hr => ?_) (by rw [m₃]; exact c₂.repr)
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [mx₆, mx₅, mx₄, mx₃, c₂.mx, mx₁]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
