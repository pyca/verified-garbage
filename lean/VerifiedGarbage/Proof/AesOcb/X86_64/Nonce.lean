import VerifiedGarbage.Proof.AesOcb.X86_64.Offset0

/-!
# AES-OCB on x86-64: `Offset_0` from the nonce (`nonce`)

Untrusted: everything here is checked by Lean. `nonce` writes `Nonce` with
its last 6 bits cleared and `bottom` (`nonceBlock_ok`), enciphers the block
(`Ktop`, `callBlocks_ok`), and computes `Offset_0` (`offset0_ok`), to
`W + ofsO` and `W + o0O` (`nonce_ok`): §4.2's `Offset_0`
(`Proof.Ocb.offset0_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (bytesAt_frame)

/-- The functions an instance calls. -/
def callees (v : BlocksImpl) : Callees := ⟨v.enc, v.dec, v.expand⟩

/-- A frame within the parts the pieces write. -/
theorem mut_of {W SP D : Addr} {n : Nat} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ mutR W SP D n, Region.Sub r r') : Frame (mutR W SP D n) m m' := h.sub hs

/-- The key schedule, after a frame within the parts the pieces write. -/
theorem ctxCiph_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    {m m' : Mem} (h : Frame (mutR W SP D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_frame h (fun r hr => (k_mut L hD r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

theorem sub_wA {W : Addr} {d k : Nat} (h : d + k ≤ 160) : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wA W) := by
  simpa using Offset.sub W (d := d) (n := k) (e := 0) (k := 160) (by omega) (by omega)

theorem sub_wB {W : Addr} {d k : Nat} (h₁ : 248 ≤ d) (h : d + k ≤ 288) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wB W) := Offset.sub W (by omega) (by omega)

theorem sub_wC {W : Addr} {d k : Nat} (h₁ : 384 ≤ d) (h : d + k ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wC W) := Offset.sub W (by omega) (by omega)

/-- A word of `W` that the pieces do not write. -/
theorem kept_read {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (mutR W SP D n) m m') {d : Nat}
    (hd : 160 ≤ d ∧ d + 8 ≤ 248 ∨ 288 ≤ d ∧ d + 8 ≤ 384) :
    m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  h.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_mut L hDW hd) (by decide)

/-- The slots, after a frame within the parts the pieces write. -/
theorem Slots.of_mut {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    {m m' : Mem} (h : Frame (mutR W SP D n) m m') {R : Nat} {N A D' : Addr} {nl n' tl : Nat}
    (S : Slots W R N A D' nl n' tl m) : Slots W R N A D' nl n' tl m' where
  data := by rw [kept_read L hDW h (by decide), S.data]
  len := by rw [kept_read L hDW h (by decide), S.len]
  tl := by rw [kept_read L hDW h (by decide), S.tl]
  rounds := by rw [kept_read L hDW h (by decide), S.rounds]
  aad := by rw [kept_read L hDW h (by decide), S.aad]
  nonce := by rw [kept_read L hDW h (by decide), S.nonce]
  nlen := by rw [kept_read L hDW h (by decide), S.nlen]

/-- What `nonce` leaves. -/
structure NonceOk (K W SP D : Addr) (n : Nat) (o : Block) (s s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (mutR W SP D n) s.mem s'.mem
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = o
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem nonce_ok (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N D : Addr} {nl t n : Nat}
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hN : s.mem.readW (W + BitVec.ofNat 64 nO) 64 = N) (hnl : s.mem.readW (W + BitVec.ofNat 64 nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64)
    (hB : Buf W SP s N nl) (hKD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (nonce (callees v)) s
      (NonceOk K W SP D n (Spec.Ocb.offset0 (ctxCiph s.mem K R) t (bytesAt s.mem N nl)) s) := by
  unfold nonce
  refine WP.seq (WP.mono (nonceBlock_ok L E hN hnl htl h1 h15 ht hB) fun s₁ P₁ => ?_)
  have E₁ : Env K W SP s₁ := E.keep (fun r hr => P₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    P₁.rd P₁.wr
  have F₁ : Frame (mutR W SP D n) s.mem s₁.mem := mut_of P₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩
  have hrnd₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [kept_read L hDW F₁ (by decide), hrnd]
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (b := v.enc) v.encOk v.encNosp v.encDepth L E₁ hR
    hrnd₁ (oneBlock_ok E₁.r15 tmpO (by decide)) (dstW L E₁.perm (d := tmpO) (n := 1) (by decide))) fun s₂ P₂ => ?_)
  have E₂ : Env K W SP s₂ := E₁.of_saved P₂.saved P₂.rd P₂.wr
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := mut_of P₂.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), sub_wC (by decide) (by decide)⟩
    · rw [E₁.rsp]; exact ⟨_, by simp, fun _ h => h⟩
  have ktop : blockAtMem s₂.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem K R (Proof.Ocb.nonceN t (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    have := P₂.enc (i := 0) (by decide)
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [this, P₁.blk]
    exact congrFun (ctxCiph_mut L hKD F₁ hR) _
  have hbv : ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat < 64 :=
    (BitVec.extractLsb' 0 6 _).isLt
  have bot₂ : s₂.mem.readW (W + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    rw [P₂.frame.readW (r := ⟨W + BitVec.ofNat 64 botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [E₁.rsp]; exact (L.stk_w' (by decide)).symm) (by decide), P₁.bot]
  obtain ⟨s₃, run₃, P₃⟩ := offset0_ok L E₂ hbv bot₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨E₂.keep (fun r hr => P₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) P₃.rd P₃.wr,
    F₁.trans (F₂.trans (mut_of P₃.frame fun r hr => ?_)), ?_, ?_, by rw [P₃.rd, P₂.rd, P₁.rd],
    by rw [P₃.wr, P₂.wr, P₁.wr]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB (by decide) (by decide)⟩
  · rw [P₃.ofs, ktop, Proof.Ocb.offset0_eq]; rfl
  · rw [P₃.o0, ktop, Proof.Ocb.offset0_eq]; rfl


end VG.Proof.AesOcb.X86_64
