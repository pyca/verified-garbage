import VerifiedGarbage.Proof.AesOcb.X86.RestTag

/-!
# AES-OCB on x86: the data (`body`)

Untrusted: everything here is checked by Lean. `body` keeps the number of
whole blocks `m = len / 16` in `W` and runs `whole` on them if there are any
(`wholeIte_ok`), then `rest` on the `len mod 16` bytes after them if there
are any (`restIte_ok`): for `seal` (`bodySeal_ok`) and `open`
(`bodyOpen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxInv ctxLstar pad)
open VG.Proof.Ocb (offAt ckOf)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off
  length_bytesAt)

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}` and `Pad`,
`pad(·)`, the variables at `[216, 384)`, the working space of the functions
called, the stack and the data. -/
abbrev bodyR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 16, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 t2O, 16⟩,
    wV p.W, wC p.W, stk p, ⟨w64 p.D, p.n⟩]

theorem bodyR_mut {p : Prm} {m m' : Mem} (h : Frame (bodyR p) m m') : Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact inMut_stk p
  · exact inMut_d p

/-- A part of `W` within `bodyR`. -/
theorem inBodyR (p : Prm) {d k : Nat}
    (h : 16 ≤ d ∧ d + k ≤ 48 ∨ 96 ≤ d ∧ d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 160 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨
      384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ bodyR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h | h
  · exact ⟨_, by simp, Offset.sub _ (e := 16) (k := 32) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 96) (k := 32) (by omega) (by omega)⟩
  · exact ⟨_, by simp, Offset.sub _ (e := 144) (k := 16) (by omega) (by omega)⟩
  · exact ⟨wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

/-- The number of whole blocks, kept in `W`. -/
theorem bodyHead_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s₁, runBlock isa [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)] s = some s₁ ∧
      s₁.mem = s.mem.writeW (w64 p.W + BitVec.ofNat 64 nbO) (BitVec.ofNat 32 (p.n / 16)) ∧
      s₁.zf = some (decide (p.n / 16 = 0)) ∧
      (∀ r, r ≠ .ebx → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have hn := L.n32
  have hl := E.slots.len
  simp only [slotv_eq] at hl
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, E.perm.wW, hl], by gmems [hl, shr4_32 hn], ?_,
    fun r h => by gregs [h], by gmems [], by gmems []⟩
  gmems [hl, shr4_32 hn, BitVec.and_self, beq_zero32 (show p.n / 16 < 2 ^ 32 by omega)]

/-- What the whole blocks leave, if there are any. -/
structure WholeIte (p : Prm) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (s t : State) : Prop where
  env : Env p t
  frame : Frame (bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  blk : ∀ k < m, blockAtMem t.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck
  tail : 0 < p.n % 16 → bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
    bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16)

theorem wholeR_body {p : Prm} {k : Nat} (hk : 16 * k ≤ p.n) {m m' : Mem} (h : Frame (wholeR p k) m m') :
    Frame (bodyR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0) {p : Prm} {G : Mem → Cipher}
    (hcall : ∀ {s s' : State} {D : BitVec 32} {n : Nat}, CallPost p f D n s s' → ∀ i < n,
      blockAtMem s'.mem (w64 D + BitVec.ofNat 64 (16 * i)) = G s.mem (blockAtMem s.mem (w64 D + BitVec.ofNat 64 (16 * i))))
    (hG : ∀ {m m' : Mem}, Frame (mutR p) m m' → G m' = G m)
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk p pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk p post (fun b o => b ^^^ o) fC2)
    (L : Lay p) {s : State} (E : Env p s) {O0 l : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i < p.n / 16, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (p.n / 16))
    (hckF2 : ∀ i < p.n / 16, ckF2 (i + 1) = fC2 (ckF2 i)
      (G s.mem (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1))) (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.mov .ebx (slot lenO), .shift .shr .ebx 4, .store (at_ .ebp nbO) .ebx,
        .alu .test .ebx (.reg .ebx)]) (.ite .e (.block []) (whole fn pre post))) s
      (WholeIte p (p.n / 16) O0 l
        (fun k => G s.mem (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (p.n / 16)) s) := by
  obtain ⟨s₁, run₁, m₁, zf₁, g₁, rd₁, wr₁⟩ := bodyHead_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fB₁ : Frame (bodyR p) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have E₁ : Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (bodyR_mut fB₁)
  have kB : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 nbO, 4⟩ →
      blockAtMem s₁.mem Q = blockAtMem s.mem Q := fun h =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  have kW : ∀ {d : Nat}, d + 16 ≤ nbO → blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 d) := fun h => kB (Lay.w_w (.inl h) (by simp only [nbO] at h; omega)
        (by decide))
  have kD : ∀ k, 16 * (k + 1) ≤ p.n → blockAtMem s₁.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) =
      blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * k)) := fun k hk =>
    kB ((L.d_w.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub (by decide)))
  have tail₁ : 0 < p.n % 16 → bytesAt s₁.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
      bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := fun hr => by
    have hd := L.dw
    have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
      rw [w64_add (by omega)]; exact Offset.sub_base _ (by omega)
    exact Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (Proof.AesOcb.X86.eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : p.n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, fB₁, rd₁, wr₁, fun k hk => absurd hk (by omega), by rw [kW (by decide), hofs, hm]; rfl,
      by rw [kW (by decide), hck, hm, hckF2₀, hm], fun hr => tail₁ hr⟩
  · have hm : p.n / 16 ≠ 0 := of_decide_eq_false h0
    have hG₁ : G s₁.mem = G s.mem := hG (bodyR_mut fB₁)
    refine WP.mono (whole_ok (O0 := O0) (l := l) (ckF1 := ckF1) (ckF2 := ckF2) ok nosp stack hcall hG hB1 hB2 L E₁
      (m := p.n / 16) (by omega) (by omega)
      (by rw [slotv_eq, m₁, Mem.readW_writeW_self32]) (by rw [kW (by decide), hofs]) (by rw [kW (by decide), ho0])
      (by rw [kW (by decide), hck]) (by rw [kW (by decide), hl0])
      (fun i hi => by rw [hckF1 i hi, kD i (by omega)]) hckF2₀
      (fun i hi => by rw [hckF2 i hi, hG₁, kD i (by omega)])) fun t P => ?_
    refine ⟨P.env, fB₁.trans (wholeR_body (Nat.mul_div_le p.n 16) P.frame), by rw [P.rd, rd₁], by rw [P.wr, wr₁],
      fun k hk => ?_, P.ofs, P.ck, fun hr => ?_⟩
    · rw [P.blk k hk, hG₁, kD k (by omega)]
    · rw [← tail₁ hr]
      have hd := L.dw
      have a16 : w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) = w64 p.D + BitVec.ofNat 64 (16 * (p.n / 16)) :=
        w64_add (by omega)
      have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
        rw [a16]; exact Offset.sub_base _ (by omega)
      exact Proof.AesGcm.X86.bytesAt_frame P.frame (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.d_w.sub_left sub).sub_right (Lay.wSub (by decide))
        · exact (L.bd.sub_right sub).symm
        · rw [a16]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)) (by omega)

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁, runBlock isa [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
        .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)] t = some t₁ ∧
      t₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧ t₁.zf = some (decide (p.n % 16 = 0)) ∧
      t₁.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 restO) (BitVec.ofNat 32 (p.n % 16)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hn := L.n32
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl
  have hsub : BitVec.ofNat 32 p.n - BitVec.ofNat 32 (p.n % 16) = BitVec.ofNat 32 (16 * (p.n / 16)) := by
    rw [sub32' (Nat.mod_le _ _) hn, show p.n - p.n % 16 = 16 * (p.n / 16) by omega]
  refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, E.perm.wW, hD, hl], by gregs [hD, hl, and15_32 hn, hsub], ?_,
    by gmems [hl, and15_32 hn], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hl, and15_32 hn, BitVec.and_self, beq_zero32 (show p.n % 16 < 2 ^ 32 by omega)]

/-- The tail of the data. -/
theorem rbuf_tail {p : Prm} (L : Lay p) {s : State} (E : Env p s) (hr : 0 < p.n % 16) :
    RBuf p s (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) (p.n % 16) := by
  have hd := L.dw
  have a16 : w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) = w64 p.D + BitVec.ofNat 64 (16 * (p.n / 16)) :=
    w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  refine ⟨by rw [toNat_add32 (by omega)]; omega, L.d_w.sub_left sub, L.bd.sub_right sub, ?_, fun r hr => ?_⟩
  · rw [a16]; exact covers_off E.perm.d (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub⟩

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (p : Prm) (P : BitVec 32) (r : Nat) (t t' : State) : Prop where
  env : Env p t'
  frame : Frame (bodyR p) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K)
    else blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem (w64 P) r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem (w64 P) r)
      (Spec.Ocb.toBytes (ctxCiph t.mem (w64 p.K) p.R
        (blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem (w64 p.K))))
    else bytesAt t.mem (w64 P) r
  ck : blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) ^^^
      pad (bytesAt (if enc then t.mem else t'.mem) (w64 P) r)
    else blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO)
  pre : bytesAt t'.mem (w64 p.D) (16 * (p.n / 16)) = bytesAt t.mem (w64 p.D) (16 * (p.n / 16))

theorem restR_body {p : Prm} {P : BitVec 32} {r : Nat}
    (hPD : Region.Sub ⟨w64 P, r⟩ ⟨w64 p.D, p.n⟩) {m m' : Mem} (h : Frame (restR p P r) m m') :
    Frame (bodyR p) m m' := h.sub fun q hq => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inBodyR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inBodyR p (.inl ⟨by decide, by decide⟩)
  · exact inBodyR p (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, hPD⟩

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.seq (.block [.mov .esi (slot dataO), .mov .eax (slot lenO), .mov .ecx (.reg .eax),
        .alu .and .ecx (imm 15), .store (at_ .ebp restO) .ecx, .alu .sub .eax (.reg .ecx), .alu .add .esi (.reg .eax),
        .alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) (rest (callees v) enc))) t
      (TailPost enc p (p.D + BitVec.ofNat 32 (16 * (p.n / 16))) (p.n % 16) t) := by
  obtain ⟨t₁, run₁, si₁, zf₁, m₁, g₁, rd₁, wr₁⟩ := bodyTail_ok L E
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fB₁ : Frame (bodyR p) t.mem t₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inBodyR p (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have E₁ : Env p t₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (bodyR_mut fB₁)
  have kB : ∀ {d : Nat}, d + 16 ≤ restO → blockAtMem t₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 d) := fun h =>
    Proof.Ocb.blockAtMem_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by simp only [restO] at h; omega)
        (by decide)
  have hK : ∀ {m : Mem}, Frame (mutR p) t.mem m → ctxLstar m (w64 p.K) = ctxLstar t.mem (w64 p.K) ∧
      ctxCiph m (w64 p.K) p.R = ctxCiph t.mem (w64 p.K) p.R := fun h => ⟨lstar_mut L h, ctxCiph_mut L h⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (Proof.AesOcb.X86.eval_e zf₁) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < p.n % 16 := by have := of_decide_eq_true h0; omega
    have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
      rw [show p.n % 16 = 0 by omega]; rfl
    have dpre : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ : Region)],
        (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint q := fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.d_w.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
    refine ⟨E₁, fB₁, rd₁, wr₁, ?_, ?_, ?_, Proof.AesGcm.X86.bytesAt_frame f₁ dpre (by have := L.dw; omega)⟩ <;>
      simp only [hr, ↓reduceIte, b0]
    · exact kB (by decide)
    · exact kB (by decide)
  · have hr : 0 < p.n % 16 := by have := of_decide_eq_false h0; omega
    have hP := rbuf_tail L E₁ hr
    have cnt₁ : slotv t₁.mem p.W restO = BitVec.ofNat 32 (p.n % 16) := by rw [slotv_eq, m₁, Mem.readW_writeW_self32]
    refine WP.mono (rest_ok v enc L E₁ hr (Nat.mod_lt _ (by decide)) si₁ cnt₁ hP) fun t' P => ?_
    have hd := L.dw
    have sub : Region.Sub ⟨w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16))), p.n % 16⟩ ⟨w64 p.D, p.n⟩ := by
      rw [w64_add (by omega)]; exact Offset.sub_base _ (by omega)
    obtain ⟨lT, cT⟩ := hK (bodyR_mut fB₁)
    have pT : bytesAt t₁.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
        bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide))) (by omega)
    have dpre : ∀ q ∈ (⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ :: restR p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
        (p.n % 16)), (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint q := by
      have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨w64 p.D, 16 * (p.n / 16)⟩ : Region).Disjoint
          ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ := fun h =>
        (L.d_w.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub h)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact dW (by decide)
      · exact (L.bd.sub_right (Region.sub_prefix (by omega))).symm
      · rw [w64_add (by omega)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    have fpre : Frame (⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩ :: restR p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
        (p.n % 16)) t.mem t'.mem :=
      (f₁.mono (by simp)).trans (P.frame.mono fun q hq => List.mem_cons_of_mem _ hq)
    refine ⟨P.env, fB₁.trans (restR_body sub P.frame), by rw [P.rd, rd₁], by rw [P.wr, wr₁],
      ?_, ?_, ?_, Proof.AesGcm.X86.bytesAt_frame fpre dpre (by omega)⟩ <;> simp only [hr, ↓reduceIte]
    · rw [P.ofs, kB (by decide), lT]
    · rw [P.out, kB (by decide), lT, cT, pT]
    · rw [P.ck, kB (by decide)]
      cases enc
      · rfl
      · simp only [↓reduceIte, pT]

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (p : Prm) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env p t
  frame : Frame (bodyR p) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem (w64 p.D) p.n = out
  ofs : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = ck

/-- The facts both `body` proofs use. -/
theorem body_facts {p : Prm} (L : Lay p) (m : Mem) :
    (∀ i < p.n / 16, blockAtMem m (w64 p.D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt m (w64 p.D) p.n) i) ∧
    (0 < p.n % 16 → (bytesAt m (w64 p.D) p.n).drop (16 * (p.n / 16)) =
      bytesAt m (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16)) := by
  have hd := L.dw
  refine ⟨fun i hi => (Proof.Ocb.blockAt_bytesAt m _ (by omega)).symm, fun hr => ?_⟩
  rw [Proof.Ocb.bytesAt_drop m _ (Nat.mul_div_le p.n 16), show p.n - 16 * (p.n / 16) = p.n % 16 by omega,
    w64_add (by omega)]

/-- The data after `body`, from its whole blocks and its rest. -/
theorem body_out {enc : Bool} {p : Prm} (L : Lay p) {t t' : State} (P : TailPost enc p (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))
    (p.n % 16) t t') {X : List Byte} (hX : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) = X) :
    bytesAt t'.mem (w64 p.D) p.n = X ++ bytesAt t'.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
  have hd := L.dw
  have e := Proof.Ocb.bytesAt_append t'.mem (w64 p.D) (16 * (p.n / 16)) (p.n % 16)
  rw [show 16 * (p.n / 16) + p.n % 16 = p.n by omega] at e
  rw [e, P.pre, hX]
  by_cases hr : 0 < p.n % 16
  · rw [w64_add (by omega)]
  · rw [show p.n % 16 = 0 by omega]; rfl

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {s : State} (E : Env p s) {O0 : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0) :
    WP isa (body (callees v) true) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K))))
      else Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K))
        (bytesAt s.mem (w64 p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)
       else offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16) ^^^
          pad ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16)) s) := by
  have hd := L.dw
  obtain ⟨hl, hrest⟩ := body_facts L s.mem
  simp only [body, ↓reduceIte]
  refine seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (w64 p.K))
    (G := fun m => ctxCiph m (w64 p.K) p.R)
    (ckF1 := ckOf fun i => blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
    v.encOk v.encNosp v.encStack (fun P _ hi => P.enc hi) (fun h => ctxCiph_mut L h) (sealPre_ok L) (xorOfs_ok L)
    L E hofs ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR p) s.mem t.mem := bodyR_mut Pw.frame
  refine WP.mono (restIte_ok v true L Pw.env) fun t' Pt => ?_
  have cT : ctxCiph t.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := ctxCiph_mut L fW
  have lT : ctxLstar t.mem (w64 p.K) = ctxLstar s.mem (w64 p.K) := lstar_mut L fW
  have blk : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine Proof.Ocb.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, hl i hi, BitVec.xor_comm]
  have ckT : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem (w64 p.D) p.n) (p.n / 16) := by
    rw [Pw.ck, Proof.Ocb.ckOf_eq hl]
  refine ⟨Pt.env, Pw.frame.trans Pt.frame, by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [body_out L Pt blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
        exact Pw.tail hr
      simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, hrest hr]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
        rw [show p.n % 16 = 0 by omega]; rfl
      simp only [hr, ↓reduceIte, b0, List.append_nil]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := by
        exact Pw.tail hr
      simp only [hr, ↓reduceIte, pT, hrest hr]
    · simp only [hr, ↓reduceIte]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {p : Prm} (L : Lay p) {s : State} (E : Env p s) {O0 : Block}
    (hofs : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (w64 p.K)) 0) :
    WP isa (body (callees v) false) s (BodyPost p
      (if 0 < p.n % 16 then
        Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K))))
      else Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K))
        (bytesAt s.mem (w64 p.D) p.n) (p.n / 16))
      (if 0 < p.n % 16 then offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)
       else offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16))
      (if 0 < p.n % 16 then
        Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
            (p.n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem (w64 p.D) p.n).drop (16 * (p.n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem (w64 p.K) p.R
              (offAt O0 (ctxLstar s.mem (w64 p.K)) (p.n / 16) ^^^ ctxLstar s.mem (w64 p.K)))))
      else Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16)) s) := by
  have hd := L.dw
  obtain ⟨hl, hrest⟩ := body_facts L s.mem
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine seq_assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (w64 p.K))
    (G := fun m => ctxInv m (w64 p.K) p.R) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => ctxInv s.mem (w64 p.K) p.R
      (blockAtMem s.mem (w64 p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (w64 p.K)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (w64 p.K)) (i + 1))
    v.decOk v.decNosp v.decStack (fun P _ hi => P.dec hi) (fun h => ctxInv_mut L h) (xorOfs_ok L) (openPost_ok L)
    L E hofs ho0 hck hl0 (fun _ _ => rfl) rfl (fun _ _ => rfl)) fun t Pw => ?_))
  have fW : Frame (mutR p) s.mem t.mem := bodyR_mut Pw.frame
  refine WP.mono (restIte_ok v false L Pw.env) fun t' Pt => ?_
  have cT : ctxCiph t.mem (w64 p.K) p.R = ctxCiph s.mem (w64 p.K) p.R := ctxCiph_mut L fW
  have lT : ctxLstar t.mem (w64 p.K) = ctxLstar s.mem (w64 p.K) := lstar_mut L fW
  have blk : bytesAt t.mem (w64 p.D) (16 * (p.n / 16)) =
      Proof.Ocb.decBlocks (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine Proof.Ocb.flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, hl i hi, Proof.Ocb.decBlock,
      BitVec.xor_comm]
  have ckT : blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (ctxInv s.mem (w64 p.K) p.R) O0 (ctxLstar s.mem (w64 p.K)) (bytesAt s.mem (w64 p.D) p.n)
        (p.n / 16) := by
    rw [Pw.ck, Proof.Ocb.ckOf_dck fun i hi => by rw [hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  refine ⟨Pt.env, Pw.frame.trans Pt.frame, by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [body_out L Pt blk, Pt.out]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := Pw.tail hr
      simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, hrest hr]
    · have b0 : ∀ (m : Mem) (q : Addr), bytesAt m q (p.n % 16) = [] := fun _ _ => by
        rw [show p.n % 16 = 0 by omega]; rfl
      simp only [hr, ↓reduceIte, b0, List.append_nil]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < p.n % 16
    · have pT : bytesAt t.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) =
          bytesAt s.mem (w64 (p.D + BitVec.ofNat 32 (16 * (p.n / 16)))) (p.n % 16) := Pw.tail hr
      simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, hrest hr]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.X86
