import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorTo
import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy

/-!
# ChaCha20 keystream XOR out of place on x86-64 with AVX-512: the rest

After the loop, fewer than 1024 bytes are left: none (`vzeroupper`), or
they are copied from the input to the output (`Gather.copyBytes_ok`) and
XORed there in place by a call of `vg_chacha20_xor_avx512` (`xor_call`), with
the state whose counter the loop advanced (`rest_ok`).
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512To

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20 VG.WriteBytes

/-! ## Memory -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (hlt : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  apply List.ext_getElem (by simp [bytesAt, hn])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    show i < xs.length by omega, ite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The output, pointwise the input XORed with `ks`. -/
theorem bytesAt_xorTo {m m' : Mem} {S D : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (D + BitVec.ofNat 64 k) = m (S + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    bytesAt m' D n = List.zipWith (· ^^^ ·) (bytesAt m S n) ks := by
  apply List.ext_getElem
  · simp [bytesAt, hks]
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by lit_omega) (by lit_omega))

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

theorem below8_24 (s : State) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) :=
  below_sub (by lit_omega) (by lit_omega)

/-! ## The call of `vg_chacha20_xor_avx512` -/

/-- A call of the implementation `v` of `vg_chacha20_xor`, with 24 bytes of
stack below `rsp`: 8 for its return address, and at most 16 for its calls
(as `ChaCha20Poly1305.X86_64.xor_call`). -/
theorem xor_call (v : XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 := below8_24 s
  have hk := v.stack_le
  have hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by lit_omega) (by lit_omega)
  have hpre : (xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
    simp only [xorStack, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
    exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
      hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩
  refine WP.call (k := xorStack v.stack) v.ok v.nosp (by lit_omega) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost, _⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by lit_omega) (by lit_omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_
  simp only [xorX86_64, State.withRegions_gpr, State.withRegions_mem,
    callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
  rw [hpost, bytesAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by lit_omega),
    Xor.stateAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

/-! ## Moves -/

theorem copyArgs_ok (s : State) :
    WP isa (.block copyArgs) s fun s' =>
      s'.gpr .r11 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .r8 ∧
      s'.gpr .rcx = s.gpr .rdx ∧
      (∀ r, r ≠ .r11 → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [copyArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, trivial, fun r h₁ h₂ h₃ h₄ => by simp [h₁, h₂, h₃, h₄], trivial, trivial,
    trivial⟩

theorem callArgs_ok (s : State) :
    WP isa (.block callArgs) s fun s' =>
      s'.gpr .rsi = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .r11 ∧ s'.gpr .rcx = s.gpr .r9 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [callArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, ↓reduceIte]
  exact ⟨trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial, trivial⟩

theorem testRdx_ok {m : Nat} (hm : m < 2 ^ 64) {s : State} (hrdx : s.gpr .rdx = BitVec.ofNat 64 m) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.zf = some (decide (m = 0)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self]
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [hrdx, ← Offset.ofNat_sub_ofNat_beq (x := m) (y := 0) hm (by decide)]
  simp

/-! ## The rest -/

theorem ret_stk (s₀ : State) : (eret s₀).Disjoint (estk s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem ret_kept {s₀ : State} (hp : APre s₀) {m : Mem} (hf : Frame (frR s₀) s₀.mem m) :
    m.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
  refine hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.ret_st
  · exact hp.ret_d
  · exact hp.ret_b

/-- The output's bytes, all written: the postcondition. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ k < eL s₀, m (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0) :
    bytesAt m (edp s₀) (eL s₀) =
      List.zipWith (· ^^^ ·) (bytesAt s₀.mem (esp s₀) (eL s₀)) (keystream (S0 s₀) (eL s₀)) :=
  bytesAt_xorTo (length_keystream _ _) h

theorem rest_ok {s₀ : State} (hp : APre s₀) {t : Nat} (ht : eL s₀ - 1024 * t < 1024) {s : State}
    (h : LInv s₀ t s) :
    WP isa restTo s fun s' => gprPreserved s₀ s' ∧ xorToX86_64.post s₀ s' := by
  have hL := eL_lt s₀
  have hle := h.le
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  refine WP.seq (WP.mono (testRdx_ok (m := eL s₀ - 1024 * t) (by omega) h.rdx)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, zf₁⟩ => ?_)
  refine WP.ite (decide (eL s₀ - 1024 * t = 0)) (by simp [eval, zf₁]) (fun hz => ?_) (fun hz => ?_)
  · have hz' : eL s₀ = 1024 * t := by have := of_decide_eq_true hz; omega
    refine WP.mono (Avx2.vz_ok s₁) fun s₂ ⟨g₂, m₂, _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · rw [g₂, g₁]; exact h.keep r hr
    · rw [m₂, m₁]; exact ret_kept hp h.frame
    · show bytesAt s₂.mem (edp s₀) (eL s₀) = _
      rw [m₂, m₁]
      exact post_of fun k hk => h.data k (by omega)
  · have hz' : 0 < eL s₀ - 1024 * t := by have := of_decide_eq_false hz; omega
    -- The rest of the input and of the output.
    have hw' : 1024 * t + (eL s₀ - 1024 * t) ≤ eL s₀ := by omega
    have sS : Region.Sub ⟨esp s₀ + BitVec.ofNat 64 (1024 * t), eL s₀ - 1024 * t⟩ (srR s₀) :=
      Offset.sub_base _ hw'
    have sD : Region.Sub ⟨edp s₀ + BitVec.ofNat 64 (1024 * t), eL s₀ - 1024 * t⟩ (edR s₀) :=
      Offset.sub_base _ hw'
    refine WP.seq (WP.mono (copyArgs_ok s₁) fun s₂ ⟨r11₂, rdi₂, rsi₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have cp : AesGcm.X86_64.Short.CopyPre s₂ (esp s₀ + BitVec.ofNat 64 (1024 * t))
        (edp s₀ + BitVec.ofNat 64 (1024 * t)) (eL s₀ - 1024 * t) :=
      ⟨by rw [rsi₂, g₁, h.r8], by rw [rdi₂, g₁, h.rsi], by rw [rcx₂, g₁, h.rdx], by omega,
        by
          rw [rd₂, wr₂, rd₁, wr₁, h.rd, h.wr, hp.rd]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨srR s₀, by simp, 1024 * t, rfl, hw'⟩,
        by
          rw [wr₂, wr₁, h.wr, hp.wr]
          refine Covers.of_sub fun r hr => ?_
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨edR s₀, by simp, 1024 * t, rfl, hw'⟩,
        (hp.s_d.sub_left sS).sub_right sD⟩
    refine WP.seq (WP.mono (ChaCha20Poly1305.X86_64.Gather.copyBytes_ok cp .z64)
      fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
    refine WP.seq (WP.mono (callArgs_ok s₃) fun s₄ ⟨rsi₄, rdi₄, rcx₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
    -- Registers at the call.
    have k₃ : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s₂.gpr r := g₃
    have e_rsi : s₄.gpr .rsi = edp s₀ + BitVec.ofNat 64 (1024 * t) := by
      rw [rsi₄, k₃ _ (by decide) (by decide) (by decide), rdi₂, g₁, h.rsi]
    have e_rdi : s₄.gpr .rdi = est s₀ := by
      rw [rdi₄, k₃ _ (by decide) (by decide) (by decide), r11₂, g₁, h.rdi]
    have e_rcx : s₄.gpr .rcx = ebp s₀ := by
      rw [rcx₄, k₃ _ (by decide) (by decide) (by decide),
        g₂ _ (by decide) (by decide) (by decide) (by decide), g₁, h.r9]
    have e_rdx : s₄.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 1024 * t) := by
      rw [g₄ _ (by decide) (by decide) (by decide), k₃ _ (by decide) (by decide) (by decide),
        g₂ _ (by decide) (by decide) (by decide) (by decide), g₁, h.rdx]
    have e_rsp : s₄.gpr .rsp = s₀.gpr .rsp := by
      rw [g₄ _ (by decide) (by decide) (by decide), k₃ _ (by decide) (by decide) (by decide),
        g₂ _ (by decide) (by decide) (by decide) (by decide), g₁, hsp]
    have keep₄ : ∀ r ∈ calleeSaved, s₄.gpr r = s₀.gpr r := fun r hr => by
      have hne : r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .rcx ∧ r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      obtain ⟨a, b, c, d, e, f, g⟩ := hne
      rw [g₄ r a b c, k₃ r d e f, g₂ r g b a c, g₁]; exact h.keep r hr
    -- Memory at the call.
    have mem₄ : s₄.mem = writeBytes s.mem (edp s₀ + BitVec.ofNat 64 (1024 * t))
        (Spec.Aes.bytesAt s.mem (esp s₀ + BitVec.ofNat 64 (1024 * t)) (eL s₀ - 1024 * t)) := by
      rw [m₄, m₃, m₂, m₁]
    have Fw : Frame [⟨edp s₀ + BitVec.ofNat 64 (1024 * t), eL s₀ - 1024 * t⟩] s.mem s₄.mem := by
      rw [mem₄]
      exact writeBytes_frame _ _ _ (by
        rw [AesGcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)
    have hS₄ : stateAt s₄.mem (est s₀) = ctr (S0 s₀) (16 * t) := by
      rw [Xor.stateAt_frame Fw (by simpa using hp.st_d.sub_right sD), h.cnt]
    have dst_wr : ∀ i < eL s₀ - 1024 * t,
        s₄.mem (edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 i) = D0 s₀ (1024 * t + i) := by
      intro i hi
      rw [mem₄, writeBytes_at _ _ _ (by omega), AesGcm.X86_64.length_bytesAt, ite_eq_left hi,
        ChaCha20Poly1305.X86_64.Gather.getD_bytesAt _ _ hi, Avx512.add_ofNat',
        src_frame hp h.frame (by omega)]
    have stk := hp.stk_st
    refine xor_call XorImpl.avx512 e_rdi e_rsi e_rdx e_rcx (by omega)
      (hp.st_d.sub_right sD) hp.st_b (hp.d_b.sub_left sD) (by have := hp.wrap_d; bv_omega)
      (by rw [e_rsp]; exact hp.stk_st) (by rw [e_rsp]; exact hp.stk_d.sub_right sD) (by rw [e_rsp]; exact hp.stk_b)
      (by
        rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, h.rd, h.wr, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
        · exact ⟨edR s₀, by simp, 1024 * t, rfl, hw'⟩
        · exact ⟨bufR s₀, by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩)
      (by
        rw [wr₄, wr₃, wr₂, wr₁, h.wr, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
        · exact ⟨edR s₀, by simp, 1024 * t, rfl, hw'⟩
        · exact ⟨bufR s₀, by simp, 0, by simp, show 0 + 320 ≤ 320 by omega⟩)
      fun s' _ _ hcs hf hpost => ?_
    rw [e_rsp] at hf
    have n_st : ∀ k < eL s₀, ¬ (stR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
      hp.st_d _ hc (in_edR hp hk)
    have n_b : ∀ k < eL s₀, ¬ (bufR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
      hp.d_b _ (in_edR hp hk) hc
    have n_sk : ∀ k < eL s₀, ¬ (estk s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun k hk hc =>
      hp.stk_d _ hc (in_edR hp hk)
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact keep₄ r hr, ?_⟩, post_of fun k hk => ?_⟩
    · refine (hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_d.sub_right sD
        · exact hp.ret_b
        · exact ret_stk s₀
      · refine (Fw.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans (ret_kept hp h.frame)
        intro r hr
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_d.sub_right sD
    · by_cases hk' : k < 1024 * t
      · have n_w : ¬ (⟨edp s₀ + BitVec.ofNat 64 (1024 * t), eL s₀ - 1024 * t⟩ : Region).Contains
            (edp s₀ + BitVec.ofNat 64 k) 1 := by
          simp only [Region.Contains]; bv_omega
        rw [hf _ (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact n_st k hk
            · exact n_w
            · exact n_b k hk
            · exact n_sk k hk), Fw _ (by simpa using n_w), h.data k hk']
      · have ea : edp s₀ + BitVec.ofNat 64 k =
            edp s₀ + BitVec.ofNat 64 (1024 * t) + BitVec.ofNat 64 (k - 1024 * t) := by
          rw [Avx512.add_ofNat', Nat.add_sub_cancel' (by omega)]
        have x := Avx2.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 1024 * t) (by omega)
        rw [dst_wr _ (by omega), ← ea, Nat.add_sub_cancel' (by omega), hS₄,
          keystream_getD _ (by omega), Avx2.ctr_ctr] at x
        rw [x, keystream_getD _ hk]
        rw [show 16 * t + (k - 1024 * t) / 64 = k / 64 by omega, show (k - 1024 * t) % 64 = k % 64 by omega]

end VG.Proof.ChaCha20.X86_64.Avx512To
