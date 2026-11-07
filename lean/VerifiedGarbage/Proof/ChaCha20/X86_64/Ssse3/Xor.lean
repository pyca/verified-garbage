module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Quad
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Quad
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Lit
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# `vg_chacha20_xor_ssse3` verified

The contract is `xorTo 16` (16 bytes of stack below the return address, for
the call of `vg_chacha20_xor` and its call of the block function), from the
source to the destination (`r11` holding the destination's distance from the
source). The loop over four blocks at a time (`Quad.lean`), with the counter
advanced by four after each 256 bytes; then the last bytes, by
`vg_chacha20_xor`; constant time.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Ssse3

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Ssse3
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2 (TPre est edp edq eL ebp edR eqR eret estk S0 D0 Q0 KS frT eL_lt
  in_dR in_eqR calleeSaved_ne ctr_ctr ctr_add pairsCode pairs_ok storeAll storeAll_frame readW_128
  readW64_off pS pQ pS_sub pQ_sub not_pQ ret_frT delta_ok)

/-! ## The invariant -/

/-- The bytes of data done before block `j`. -/
abbrev P (s₀ : State) (j : Nat) : Nat := min (64 * j) (eL s₀)

theorem P_le (s₀ : State) (j : Nat) : P s₀ j ≤ eL s₀ := Nat.min_le_right _ _

/-- Before block `j` (the loop's invariant); the counter (word 12 of the
state) is block `j`'s while there are bytes left. -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (P s₀ j)
  r11 : s.gpr .r11 = edq s₀ - edp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - P s₀ j)
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : P s₀ j < eL s₀ → stateAt s.mem (est s₀) = ctr (S0 s₀) j
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k
  masks : Masks (ebp s₀) s.mem
  frame : Frame (frT s₀) s₀.mem s.mem

theorem OInv.of {s₀ : State} {j : Nat} {s s' : State} (h : OInv s₀ j s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : OInv s₀ j s' :=
  ⟨by rw [hg, h.rdi], by rw [hg, h.rcx], by rw [hg, h.rsi], by rw [hg, h.r11], by rw [hg, h.rdx],
    fun r hr' => by rw [hg, h.keep r hr'], by rw [hr, h.rd], by rw [hw, h.wr],
    fun hl => by rw [hm]; exact h.cnt hl, fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.masks,
    by rw [hm]; exact h.frame⟩

/-- The source from block `j` on is intact. -/
theorem OInv.src {s₀ : State} (hp : TPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) {k : Nat}
    (hpk : P s₀ j ≤ k) (hk : k < eL s₀) : s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k :=
  hp.src_of h.data h.frame hpk hk

/-! ## The prologue -/

/-- The offsets in `buf` and values of the quadwords of `masks`. -/
def maskPairs : List (Nat × BitVec 64) :=
  [(272, 0x0504070601000302), (280, 0x0d0c0f0e09080b0a), (288, 0x0605040702010003),
   (296, 0x0e0d0c0f0a09080b)]

theorem masks_eq : masks = pairsCode maskPairs := rfl

theorem maskPairs_le : ∀ p ∈ maskPairs, p.1 + 8 ≤ 320 := by decide

/-- Read back a stored quadword. -/
local macro "qread" : tactic => `(tactic|
  plain_simp_names simp (disch := decide) only [storeAll, maskPairs, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, readW64_off, Mem.readW_writeW_self64])

theorem masks_mem (m : Mem) (buf : Addr) : Masks buf (storeAll buf maskPairs m) := by
  have e : ∀ d, buf + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = buf + BitVec.ofNat 64 (d + 8) :=
    fun d => Offset.add_add _ _ _
  refine ⟨?_, ?_⟩
  · rw [rot16Off, readW_128, e]
    have h0 : (storeAll buf maskPairs m).readW (buf + BitVec.ofNat 64 272) 64 = 0x0504070601000302 := by qread
    have h1 : (storeAll buf maskPairs m).readW (buf + BitVec.ofNat 64 (272 + 8)) 64 = 0x0d0c0f0e09080b0a := by
      qread
    rw [h0, h1]; decide
  · rw [rot8Off, readW_128, e]
    have h0 : (storeAll buf maskPairs m).readW (buf + BitVec.ofNat 64 288) 64 = 0x0605040702010003 := by qread
    have h1 : (storeAll buf maskPairs m).readW (buf + BitVec.ofNat 64 (288 + 8)) 64 = 0x0e0d0c0f0a09080b := by
      qread
    rw [h0, h1]; decide

theorem prologue_ok {s₀ : State} (hp : TPre s₀) :
    WP isa (.block (masks ++ Impl.ChaCha20.X86_64.XorBuf.delta ++ ([.alu .cmp .rdx (.imm 65)] : List Instr)))
      s₀ fun s => OInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 65)) := by
  rw [masks_eq]
  refine WP.block_append (WP.block_append (WP.mono (pairs_ok maskPairs maskPairs_le (s := s₀) rfl hp.w_b)
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (delta_ok s₁) fun s₂ ⟨d₂, g₂, m₂, rd₂, wr₂, _⟩ =>
      WP.mono (cmpi_ok s₂ .rdx (n := 65) (by decide)) fun s₃ ⟨g₃, m₃, _, rd₃, wr₃, cf₃⟩ => ?_))
  have F : Frame [Avx2.bufR (ebp s₀)] s₀.mem s₃.mem := by
    rw [m₃, m₂, m₁]; exact storeAll_frame (List.mem_singleton_self _) _ maskPairs_le _
  have gk : ∀ r, r ≠ .rax → r ≠ .r11 → s₃.gpr r = s₀.gpr r := fun r hr h11 => by
    rw [g₃, g₂ r h11, g₁ r hr]
  refine ⟨⟨gk _ (by decide) (by decide), gk _ (by decide) (by decide),
    by rw [gk _ (by decide) (by decide)]; simp,
    by rw [g₃, d₂, g₁ _ (by decide), g₁ _ (by decide)],
    by rw [gk _ (by decide) (by decide)]; simp, fun r hr => gk r (calleeSaved_ne hr).1 (by
      intro h; subst h; simp [calleeSaved] at hr),
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun _ => ?_, fun k hk => ?_, ?_, ?_⟩, ?_⟩
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), ctr_zero]
  · rw [F _ (by simpa using fun hc => hp.q_b _ (in_eqR hk) hc)]
    simp
  · rw [m₃, m₂, m₁]; exact masks_mem _ _
  · exact F.mono (by simp)
  · rw [cf₃, g₂ _ (by decide), g₁ _ (by decide)]

/-! ## Four blocks at once -/

theorem ctx_of {s₀ : State} (hp : TPre s₀) {s : State} (hb : s.gpr .rdi = est s₀)
    (hd : s.gpr .rcx = ebp s₀) (hw : s.wr = s₀.wr) : Ctx (est s₀) (ebp s₀) s :=
  ⟨fun d _ => by rw [ea_at, hb], fun d _ => by rw [ea_at, hd],
   by rw [hw]; exact hp.w_st, by rw [hw]; exact hp.w_b, hp.st_b⟩

/-- The data of the four blocks after `j`. -/
abbrev win (s₀ : State) (j : Nat) : Addr := edp s₀ + BitVec.ofNat 64 (P s₀ j)

/-- The destination of the four blocks after `j`. -/
abbrev winQ (s₀ : State) (j : Nat) : Addr := edq s₀ + BitVec.ofNat 64 (P s₀ j)

/-- How many bytes of data the four blocks after `j` are for. -/
abbrev Wn (s₀ : State) (j : Nat) : Nat := min (eL s₀ - P s₀ j) 256

theorem Wn_le (s₀ : State) (j : Nat) : Wn s₀ j ≤ eL s₀ - P s₀ j ∧ Wn s₀ j ≤ 256 :=
  ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

theorem dW_sub (s₀ : State) (j : Nat) : Region.Sub (dW (win s₀ j) (Wn s₀ j)) (edR s₀) :=
  Offset.sub_base _ (by have := P_le s₀ j; have := Wn_le s₀ j; omega)
theorem dWq_sub (s₀ : State) (j : Nat) : Region.Sub (dW (winQ s₀ j) (Wn s₀ j)) (eqR s₀) :=
  Offset.sub_base _ (by have := P_le s₀ j; have := Wn_le s₀ j; omega)

theorem win_alias {s₀ : State} (hp : TPre s₀) (j : Nat) :
    winQ s₀ j = win s₀ j ∨ (dW (win s₀ j) (Wn s₀ j)).Disjoint (dW (winQ s₀ j) (Wn s₀ j)) := by
  rcases hp.alias with he | hdis
  · exact .inl (by simp only [winQ, win, he])
  · exact .inr ((hdis.sub_left (dW_sub s₀ j)).sub_right (dWq_sub s₀ j))

theorem dctx_of {s₀ : State} (hp : TPre s₀) {j : Nat} {s : State}
    (hsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (P s₀ j)) (h11 : s.gpr .r11 = edq s₀ - edp s₀)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) :
    DCtx (win s₀ j) (winQ s₀ j) (Wn s₀ j) s :=
  ⟨fun d _ => by rw [ea_at, hsi],
   fun d _ => by rw [XorBuf.ea_atDst_eq s hsi h11, ← Offset.add_add],
   fun off n h => ⟨edR s₀, by rw [hr, hw, hp.rd]; simp, by
      have := eL_lt s₀
      have := P_le s₀ j
      have := Wn_le s₀ j
      rw [Offset.add_add]; exact Xor.contains_ofNat (by omega) (by lit_omega)⟩,
   fun off n h => ⟨eqR s₀, by rw [hw, hp.wr]; simp, by
      have := eL_lt s₀
      have := P_le s₀ j
      have := Wn_le s₀ j
      rw [Offset.add_add]; exact Xor.contains_ofNat (by omega) (by lit_omega)⟩,
   win_alias hp j⟩

/-- The regions four blocks write: the slots, the counters and `buf[0, 16)`
in `buf`, the data of the four blocks, and the state (its counter). -/
abbrev qR (s₀ : State) (j : Nat) : List Region :=
  [slotsR (ebp s₀), ctrR (ebp s₀), dW (winQ s₀ j) (Wn s₀ j), stashR (ebp s₀), Avx2.stR (est s₀)]

theorem slots_sub (s₀ : State) : Region.Sub (slotsR (ebp s₀)) (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by decide)
theorem ctrR_sub (s₀ : State) : Region.Sub (ctrR (ebp s₀)) (Avx2.bufR (ebp s₀)) := Offset.sub_base _ (by decide)
theorem stash_sub (s₀ : State) : Region.Sub (stashR (ebp s₀)) (Avx2.bufR (ebp s₀)) := Region.sub_prefix (by decide)
theorem kR_sub (s₀ : State) : Region.Sub (kR (ebp s₀)) (Avx2.bufR (ebp s₀)) := Offset.sub_base _ (by decide)
theorem qR_frame (s₀ : State) (j : Nat) : ∀ r ∈ qR s₀ j, ∃ r' ∈ frT s₀, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨Avx2.bufR (ebp s₀), by simp, slots_sub s₀⟩
  · exact ⟨Avx2.bufR (ebp s₀), by simp, ctrR_sub s₀⟩
  · exact ⟨eqR s₀, by simp, dWq_sub s₀ j⟩
  · exact ⟨Avx2.bufR (ebp s₀), by simp, stash_sub s₀⟩
  · exact ⟨Avx2.stR (est s₀), by simp, fun _ h => h⟩

/-- What the four blocks write is outside `buf[272, 304)`. -/
theorem kR_qR {s₀ : State} (hp : TPre s₀) (j : Nat) : ∀ r ∈ qR s₀ j, (kR (ebp s₀)).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact kR_slots _
  · exact Offset.disjoint _ (by simp only [ctrOff, rot16Off]; omega_using []) (by decide) (by decide)
  · exact (hp.q_b.symm.sub_left (kR_sub s₀)).sub_right (dWq_sub s₀ j)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact hp.st_b.symm.sub_left (kR_sub s₀)

/-- The keystream of the four blocks after `j`: the rounds' result plus the
input states, the counter being block `j`'s. -/
abbrev B4 (C : CState) : Nat → CState :=
  blk (fun l => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr C l)) C

theorem ksb_eq {s₀ : State} {j t : Nat} (hPj : P s₀ j = 64 * j) (ht : P s₀ j + t < eL s₀) :
    ksb (B4 (ctr (S0 s₀) j)) t = (KS s₀).getD (P s₀ j + t) 0 := by
  show (serialize (Spec.ChaCha20.block (ctr (ctr (S0 s₀) j) (t / 64)))).getD (t % 64) 0 = _
  rw [KS, keystream_getD _ ht, ctr_ctr, hPj, show j + t / 64 = (64 * j + t) / 64 by omega_using [],
    show t % 64 = (64 * j + t) % 64 by omega_using []]

/-- What the setup, the rounds and the output leave: the keystream XORed
with the source in the destination (but for the bytes past the last multiple
of 16, if any, whose keystream is in `buf[0, 16)`), and everything else as it
was but `rax` and the regions of `qR` (not the state). -/
structure Q4 (s₀ : State) (j : Nat) (s s' : State) : Prop where
  data : ∀ k, k < Wn s₀ j → s'.mem (winQ s₀ j + BitVec.ofNat 64 k) =
    if Full (Wn s₀ j) k then
      s.mem (win s₀ j + BitVec.ofNat 64 k) ^^^ ksb (B4 (stateAt s.mem (est s₀))) k
    else s.mem (winQ s₀ j + BitVec.ofNat 64 k)
  stash : Stashed (ebp s₀) (B4 (stateAt s.mem (est s₀))) (Wn s₀ j) (fun _ => True) s'.mem
  keep : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [slotsR (ebp s₀), ctrR (ebp s₀), dW (winQ s₀ j) (Wn s₀ j), stashR (ebp s₀)] s.mem s'.mem
  st : stateAt s'.mem (est s₀) = stateAt s.mem (est s₀)

theorem Q4.of {s₀ : State} {j : Nat} {s s₃ s₄ : State} (h : Q4 s₀ j s s₃) (hg : s₄.gpr = s₃.gpr)
    (hm : s₄.mem = s₃.mem) (hr : s₄.rd = s₃.rd) (hw : s₄.wr = s₃.wr) : Q4 s₀ j s s₄ :=
  ⟨fun k hk => by rw [hm]; exact h.data k hk, fun a b => by rw [hm]; exact h.stash a b,
    fun r hr' => by rw [hg]; exact h.keep r hr', by rw [hr, h.rd], by rw [hw, h.wr], hm ▸ h.frame,
    by rw [hm]; exact h.st⟩

theorem quad4_ok {s₀ : State} (hp : TPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s)
    {C : Prog isa} {Q : State → Prop} (hk : ∀ s₃, Q4 s₀ j s s₃ → WP isa C s₃ Q) :
    WP isa (.seq (.block setup4) (.seq rounds10 (.seq finish4 C))) s Q := by
  have hL := eL_lt s₀
  have hc := ctx_of hp h.rdi h.rcx h.wr
  have sl_st : (Avx2.stR (est s₀)).Disjoint (slotsR (ebp s₀)) := hp.st_b.sub_right (slots_sub s₀)
  have ct_st : (Avx2.stR (est s₀)).Disjoint (ctrR (ebp s₀)) := hp.st_b.sub_right (ctrR_sub s₀)
  have da : (dW (win s₀ j) (Wn s₀ j)).Disjoint (bufR (ebp s₀)) := hp.d_b.sub_left (dW_sub s₀ j)
  have db : (dW (winQ s₀ j) (Wn s₀ j)).Disjoint (bufR (ebp s₀)) := hp.q_b.sub_left (dWq_sub s₀ j)
  have ds : (dW (winQ s₀ j) (Wn s₀ j)).Disjoint (stR (est s₀)) := hp.st_q.symm.sub_left (dWq_sub s₀ j)
  -- The setup.
  refine WP.seq (WP.mono (setup4_ok hc) fun s₁ h₁ => ?_)
  have hc₁ : Ctx (est s₀) (ebp s₀) s₁ := ctx_of hp (by rw [h₁.keep _ (by decide), h.rdi])
    (by rw [h₁.keep _ (by decide), h.rcx]) (by rw [h₁.wr, h.wr])
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok hc₁.eaB hc₁.wb (h.masks.frame h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact kR_qR hp j _ (by simp)
      · exact kR_qR hp j _ (by simp))) h₁.holds) fun s₂ h₂ => ?_)
  have hc₂ : Ctx (est s₀) (ebp s₀) s₂ := hc₁.of h₂.gpr h₂.wr
  have hg₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr => by rw [h₂.gpr, h₁.keep r hr]
  have hd₂ : DCtx (win s₀ j) (winQ s₀ j) (Wn s₀ j) s₂ := dctx_of hp (by rw [hg₂ _ (by decide), h.rsi])
    (by rw [hg₂ _ (by decide), h.r11]) (by rw [h₂.rd, h₁.rd, h.rd]) (by rw [h₂.wr, h₁.wr, h.wr])
  have hct₂ : Ctrs (ebp s₀) (stateAt s.mem (est s₀)) 4 s₂.mem := fun l hl => by
    rw [h₂.frame.readW (r := ctrR (ebp s₀)) (Offset.contains _ (by omega_using []) (by omega_using [hl]) (by decide))
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by decide)]
    exact h₁.ctrs l hl
  have hC₂ : stateAt s₂.mem (est s₀) = stateAt s.mem (est s₀) :=
    (stateAt_frame h₂.frame (by simpa using sl_st)).trans
      (stateAt_frame h₁.frame (by simpa using ⟨sl_st, ct_st⟩))
  -- The output.
  refine WP.seq (WP.mono (finish4_ok hc₂ hd₂ (n := eL s₀ - P s₀ j) (by omega_using [hL]) rfl
    (by rw [hg₂ _ (by decide), h.rdx]) db da ds h₂.holds hct₂ hC₂) fun s₃ h₃ => hk s₃ ?_)
  have hf₃ : Frame [slotsR (ebp s₀), ctrR (ebp s₀), dW (winQ s₀ j) (Wn s₀ j), stashR (ebp s₀)] s.mem s₃.mem :=
    ((h₁.frame.mono (by simp)).trans (h₂.frame.mono (by simp))).trans (h₃.frame.mono (by simp))
  have hW : Wn s₀ j ≤ 256 := Nat.min_le_right _ _
  refine ⟨fun k hk => ?_, fun hz _ => h₃.stash hz (by simp only [sOff]; omega_using []),
    fun r hr => by rw [h₃.gpr, hg₂ r hr], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr], hf₃, ?_⟩
  · have e₂ : ∀ a, (dW a (Wn s₀ j)).Disjoint (bufR (ebp s₀)) →
        s₂.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) := fun a hb =>
      (h₁.frame.trans (h₂.frame.mono (by simp))).bytes (R := dW a (Wn s₀ j))
        (by simpa using ⟨hb.sub_right (Region.sub_prefix (by decide)),
          hb.sub_right (Offset.sub_base _ (by decide))⟩)
        (show Wn s₀ j ≤ 2 ^ 64 by omega_using [hW]) hk
    rw [h₃.data k hk]
    by_cases c : Full (Wn s₀ j) k
    · rw [ite_eq_left ⟨by omega_using [], c⟩, ite_eq_left c, e₂ _ da]
    · rw [ite_eq_right (by omega), ite_eq_right c, e₂ _ db]
  · exact stateAt_frame hf₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact sl_st
      · exact ct_st
      · exact ds.symm
      · exact hp.st_b.sub_right (stash_sub s₀))

/-- The destination before four blocks `j` that `Q4` leaves: what it was,
outside the `W` bytes of the four blocks. -/
theorem Q4.outside {s₀ : State} (hp : TPre s₀) {j : Nat} {s s₃ : State} (h₃ : Q4 s₀ j s s₃) {k : Nat}
    (hk : k < eL s₀) (hw : ¬ (P s₀ j ≤ k ∧ k < P s₀ j + Wn s₀ j)) :
    s₃.mem (edq s₀ + BitVec.ofNat 64 k) = s.mem (edq s₀ + BitVec.ofNat 64 k) := by
  have hL := eL_lt s₀
  have := P_le s₀ j
  have := Wn_le s₀ j
  refine h₃.frame _ fun r hr => ?_
  have hin : (eqR s₀).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := in_eqR hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.q_b.sub_right (slots_sub s₀)) _ hin
  · exact (hp.q_b.sub_right (ctrR_sub s₀)) _ hin
  · simp only [Region.Contains]
    rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
    split <;> omega
  · exact (hp.q_b.sub_right (stash_sub s₀)) _ hin

/-- The source of the four blocks `j` that `Q4` leaves: what it was, past
the multiples of 16. -/
theorem Q4.src {s₀ : State} (hp : TPre s₀) {j : Nat} {s s₃ : State} (h₃ : Q4 s₀ j s s₃) {t : Nat}
    (ht : t < Wn s₀ j) (hc : ¬ Full (Wn s₀ j) t) :
    s₃.mem (win s₀ j + BitVec.ofNat 64 t) = s.mem (win s₀ j + BitVec.ofNat 64 t) :=
  src_keep (Wn_le s₀ j).2 (win_alias hp j) (rs := [slotsR (ebp s₀), ctrR (ebp s₀), stashR (ebp s₀)])
    (by
      have da : (dW (win s₀ j) (Wn s₀ j)).Disjoint (Avx2.bufR (ebp s₀)) := hp.d_b.sub_left (dW_sub s₀ j)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact da.sub_right (slots_sub s₀)
      · exact da.sub_right (ctrR_sub s₀)
      · exact da.sub_right (stash_sub s₀))
    (h₃.frame.mono (by simp)) (fun t ht hc => by rw [h₃.data t ht, ite_eq_right hc]) ht hc

/-! ## The end of four blocks -/

theorem next_eq : next4 = [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 4),
    .store32 (at_ .rdi 48) .rax, .alu .add .rsi (.imm 256), .alu .sub .rdx (.imm 256)] := rfl

set_option simprocs false in
/-- More than 256 bytes left: the counter advanced by 4, and the data by 256 bytes. -/
theorem next_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j + 257 ≤ eL s₀) {s s₃ : State}
    (h : OInv s₀ j s) (h₃ : Q4 s₀ j s s₃) :
    WP isa (.block next4) s₃ fun s' => OInv s₀ (j + 4) s' ∧ Frame [Avx2.stR (est s₀)] s₃.mem s'.mem := by
  have hL := eL_lt s₀
  have hPj : P s₀ j = 64 * j := by simp only [P] at *; omega
  have hP4 : P s₀ (j + 4) = P s₀ j + 256 := by simp only [P] at *; omega
  have hW : Wn s₀ j = 256 := by simp only [Wn]; omega
  have hcnt := h.cnt (by omega)
  have hrdi : s₃.gpr .rdi = est s₀ := by rw [h₃.keep _ (by decide), h.rdi]
  have c₁ : (Avx2.stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s₃.rd ++ s₃.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨Avx2.stR (est s₀), by simp [h₃.rd, h₃.wr, h.rd, h.wr, hp.wr], c₁⟩
  have o₁ : InRegions s₃.wr (Xor.off (est s₀) 48) 4 := ⟨Avx2.stR (est s₀), by simp [h₃.wr, h.wr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  rw [next_eq]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s₃.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (ctr (S0 s₀) j)[12]'(by decide) := by
    rw [← hcnt, ← h₃.st]; simp [stateAt]
  rw [hv]
  have se : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  have fW : Frame [Avx2.stR (est s₀)] s₃.mem
      (s₃.mem.writeW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) ((ctr (S0 s₀) j)[12]'(by decide) + 4)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hf : Frame (qR s₀ j) s.mem
      (s₃.mem.writeW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) ((ctr (S0 s₀) j)[12]'(by decide) + 4)) :=
    (h₃.frame.mono (by simp)).trans (fW.mono (by simp))
  have hg : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₃.gpr r = s.gpr r := fun r h1 _ _ => h₃.keep r h1
  refine ⟨⟨by simp (config := {decide := true}) only [ite_false]; exact hrdi,
    by simp (config := {decide := true}) only [ite_false]; rw [hg _ (by decide) (by decide) (by decide), h.rcx],
    ?_, ?_, ?_, fun r hr => ?_, by rw [h₃.rd, h.rd], by rw [h₃.wr, h.wr], fun _ => ?_, fun k hk => ?_, ?_,
    h.frame.trans (hf.sub (qR_frame s₀ j))⟩, fW⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [h₃.keep _ (by decide), h.rsi, se, Offset.add_add, hP4]
  · simp (config := {decide := true}) only [ite_false]
    rw [hg _ (by decide) (by decide) (by decide), h.r11]
  · simp (config := {decide := true}) only [ite_true]
    rw [h₃.keep _ (by decide), h.rdx, se, Offset.ofNat_sub_ofNat (by lit_omega), hP4, Nat.sub_sub]
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    simp only [a, b, c, ite_false]; rw [hg r a b c]; exact h.keep r hr
  · dsimp only
    rw [Xor.stateAt_writeW_counter, h₃.st, hcnt, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ctr_add]
  · -- The data.
    dsimp only
    have e₁ : (s₃.mem.writeW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) ((ctr (S0 s₀) j)[12]'(by decide) + 4))
        (edq s₀ + BitVec.ofNat 64 k) = s₃.mem (edq s₀ + BitVec.ofNat 64 k) :=
      fW.bytes (R := eqR s₀) (by simpa using hp.st_q.symm) (show eL s₀ ≤ 2 ^ 64 by omega) hk
    rw [e₁]
    by_cases hw : P s₀ j ≤ k ∧ k < P s₀ j + 256
    · have ea : edq s₀ + BitVec.ofNat 64 k = winQ s₀ j + BitVec.ofNat 64 (k - P s₀ j) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hw.1]
      have ea' : edp s₀ + BitVec.ofNat 64 k = win s₀ j + BitVec.ofNat 64 (k - P s₀ j) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hw.1]
      rw [ea, h₃.data _ (by omega), ite_eq_left (by simp only [Full]; omega), ← ea', h.src hp hw.1 hk,
        ite_eq_left (by omega : k < P s₀ (j + 4)), hcnt,
        ksb_eq hPj (by omega), Nat.add_sub_cancel' hw.1]
    · rw [h₃.outside hp hk (by omega), h.data k hk]
      by_cases hk' : k < P s₀ j
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · exact h.masks.frame hf (kR_qR hp j)

/-! ## The last bytes of four blocks -/

theorem and_m16 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& (0xfffffff0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n / 16 * 16) := by
  have : (0xfffffff0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 ((2 ^ 60 - 1) <<< 4) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  have h1 : (2 ^ 60 - 1) <<< 4 < 2 ^ 64 := by decide
  have h2 : n / 16 * 16 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2]
  rw [show n / 16 * 16 = (n >>> 4) <<< 4 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h : 4 ≤ i
  · by_cases h' : i - 4 < 60
    · simp [h, h', show 4 + (i - 4) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 64 := hn
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [h, h', this]
  · simp [h]

theorem and_15 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n % 16) := by
  have : (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (2 ^ 4 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 2 ^ 4 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show n % 2 ^ 4 < 2 ^ 64 by omega)]

theorem last_eq : last = .seq (.block [.mov .r9 (.reg .rcx), .mov .rax (.reg .rdx),
    .alu .and .rax (.imm 0xfffffff0), .alu .add .rsi (.reg .rax), .alu .and .rdx (.imm 15),
    .mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi)])
    (.seq (Impl.ChaCha20.X86_64.XorBuf.xorBufTo .r10 .rsi .r9)
      (.block [.mov .rcx (.reg .r9), .alu .add .rsi (.reg .rdx), .mov32 .rdx (.imm 0)])) := rfl

theorem lastPre_ok {s₀ : State} {j : Nat} {s₃ : State} {n : Nat} (hn : n < 2 ^ 64)
    (hrcx : s₃.gpr .rcx = ebp s₀) (hrsi : s₃.gpr .rsi = edp s₀ + BitVec.ofNat 64 (P s₀ j))
    (hr11 : s₃.gpr .r11 = edq s₀ - edp s₀) (hrdx : s₃.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .r9 (.reg .rcx), .mov .rax (.reg .rdx),
      .alu .and .rax (.imm 0xfffffff0), .alu .add .rsi (.reg .rax), .alu .and .rdx (.imm 15),
      .mov .r10 (.reg .r11), .alu .add .r10 (.reg .rsi)]) s₃
      fun s₄ => s₄.gpr .r9 = ebp s₀ ∧
        s₄.gpr .rsi = edp s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16) ∧
        s₄.gpr .r10 = edq s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16) ∧
        s₄.gpr .rdx = BitVec.ofNat 64 (n % 16) ∧
        (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s₃.gpr r) ∧
        s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setReg,
    State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, trivial, trivial, trivial⟩
  · simp only [reduceCtorEq, ↓reduceIte, hrcx]
  · simp only [reduceCtorEq, ↓reduceIte, hrsi, hrdx, and_m16 hn, Offset.add_add]
  · simp only [reduceCtorEq, ↓reduceIte, hrsi, hrdx, hr11, and_m16 hn, Offset.add_add, XorBuf.sub_add_add]
  · simp only [reduceCtorEq, ↓reduceIte, hrdx, and_15 hn]
  · simp only [h1, h2, h3, h4, h5, ite_false]

theorem lastPost_ok {s : State} :
    WP isa (.block [.mov .rcx (.reg .r9), .alu .add .rsi (.reg .rdx), .mov32 .rdx (.imm 0)]) s
      fun s' => s'.gpr .rcx = s.gpr .r9 ∧ s'.gpr .rsi = s.gpr .rsi + s.gpr .rdx ∧
        s'.gpr .rdx = 0 ∧ (∀ r, r ≠ .rcx → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags,
    State.setReg, State.setReg32, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_, trivial, trivial, trivial⟩
  · simp only [reduceCtorEq, ↓reduceIte]
  · simp only [reduceCtorEq, ↓reduceIte]
  · simp only [↓reduceIte]; rfl
  · simp only [h1, h2, h3, ite_false]

/-- At most 256 bytes left: the bytes after the last multiple of 16 XORed
with the keystream in `buf[0, 16)`, and no bytes left. -/
theorem last_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j + 65 ≤ eL s₀) (hle : eL s₀ ≤ P s₀ j + 256)
    {s s₃ : State} (h : OInv s₀ j s) (h₃ : Q4 s₀ j s s₃) :
    WP isa last s₃ fun s' => OInv s₀ (j + 4) s' ∧ Frame [eqR s₀] s₃.mem s'.mem := by
  have hL := eL_lt s₀
  have hPj : P s₀ j = 64 * j := by simp only [P] at *; omega
  have hP4 : P s₀ (j + 4) = eL s₀ := by simp only [P] at *; omega
  have hW : Wn s₀ j = eL s₀ - P s₀ j := by simp only [Wn]; omega
  have hcnt := h.cnt (by omega)
  generalize hn : eL s₀ - P s₀ j = n at hW
  have hq : n / 16 * 16 ≤ n := Nat.div_mul_le_self n 16
  rw [last_eq]
  refine WP.seq (WP.mono (lastPre_ok (s₀ := s₀) (j := j) (n := n) (by omega) (by rw [h₃.keep _ (by decide), h.rcx])
    (by rw [h₃.keep _ (by decide), h.rsi]) (by rw [h₃.keep _ (by decide), h.r11])
    (by rw [h₃.keep _ (by decide), h.rdx, hn]))
    fun s₄ ⟨r9₄, rsi₄, r10₄, rdx₄, g₄, m₄, rd₄, wr₄⟩ => ?_)
  have hDs : Region.Sub ⟨edp s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16), n % 16⟩ (edR s₀) :=
    Offset.sub_base _ (by omega)
  have hQs : Region.Sub ⟨edq s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16), n % 16⟩ (eqR s₀) :=
    Offset.sub_base _ (by omega)
  have hsep : XorBuf.Sep (edq s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16))
      (edp s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16)) (ebp s₀) (n % 16) :=
    ⟨(hp.q_b.sub_left hQs).sub_right (Region.sub_prefix (by omega)), by
      rcases hp.alias with he | hdis
      · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
      · exact .inr ((hdis.sub_left hDs).sub_right hQs), by omega⟩
  have hwD : InRegions s₄.wr (edq s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16)) (n % 16) :=
    ⟨eqR s₀, by rw [wr₄, h₃.wr, h.wr]; exact hp.w_q, Xor.contains_ofNat (by omega) (by omega)⟩
  have hrS : InRegions (s₄.rd ++ s₄.wr) (edp s₀ + BitVec.ofNat 64 (P s₀ j + n / 16 * 16)) (n % 16) :=
    ⟨edR s₀, by rw [rd₄, wr₄, h₃.rd, h₃.wr, h.rd, h.wr]; exact hp.r_d, Xor.contains_ofNat (by omega) (by omega)⟩
  have hrB : InRegions (s₄.rd ++ s₄.wr) (ebp s₀) (n % 16) :=
    ⟨Avx2.bufR (ebp s₀), List.mem_append_right _ (by rw [wr₄, h₃.wr, h.wr]; exact hp.w_b), by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine WP.seq (WP.mono (XorBuf.xorBufTo_ok (d := .r10) (sr := .rsi) (b := .r9) (by decide) (by decide)
    (by decide) r10₄ rsi₄ r9₄ rdx₄ hsep hwD hrS hrB) fun s₅ po => ?_)
  refine WP.mono lastPost_ok fun s' ⟨rcx', rsi', rdx', g', m', rd', wr'⟩ => ?_
  have hk5 : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rsi → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 →
      s'.gpr r = s.gpr r :=
    fun r a b c d e f g => by rw [g' r c d e, po.keep r a b c, g₄ r a d e f g, h₃.keep r a]
  have hm' : s'.mem = s₅.mem := m'
  -- The bytes `xorBufTo` wrote.
  have hDf : Frame [eqR s₀] s₄.mem s₅.mem := po.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨eqR s₀, List.mem_singleton_self _, hQs⟩
  have hf : Frame (frT s₀) s.mem s'.mem :=
    (h₃.frame.sub fun r hr => qR_frame s₀ j r (by
      simp only [qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)).trans (hm' ▸ m₄ ▸ hDf.mono (by simp))
  refine ⟨⟨by rw [hk5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.rdi],
    by rw [rcx', po.keep _ (by decide) (by decide) (by decide), r9₄], ?_,
    by rw [hk5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r11],
    ?_, fun r hr => ?_,
    by rw [rd', po.rd, rd₄, h₃.rd, h.rd], by rw [wr', po.wr, wr₄, h₃.wr, h.wr],
    fun hlt => absurd hlt (by omega), fun k hk => ?_, ?_, h.frame.trans hf⟩, by rw [hm', ← m₄]; exact hDf⟩
  · rw [rsi', po.keep _ (by decide) (by decide) (by decide), po.keep _ (by decide) (by decide) (by decide),
      rsi₄, rdx₄, Offset.add_add, hP4]
    congr 2; omega
  · rw [rdx', hP4, Nat.sub_self]; rfl
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    have hr' : r ≠ .r8 ∧ r ≠ .rcx ∧ r ≠ .r9 ∧ r ≠ .r10 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hk5 r a hr'.1 hr'.2.1 b c hr'.2.2.1 hr'.2.2.2]; exact h.keep r hr
  · -- The destination.
    rw [ite_eq_left (by omega), hm']
    have hout : ∀ k, k < P s₀ j + n / 16 * 16 →
        s₅.mem (edq s₀ + BitVec.ofNat 64 k) = s₄.mem (edq s₀ + BitVec.ofNat 64 k) :=
      fun k hk' => po.frame _ fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains] at hcon
        rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
        split at hcon <;> omega
    have hwin : ∀ t, win s₀ j + BitVec.ofNat 64 t = edp s₀ + BitVec.ofNat 64 (P s₀ j + t) :=
      fun t => Offset.add_add _ _ _
    have hwinQ : ∀ t, winQ s₀ j + BitVec.ofNat 64 t = edq s₀ + BitVec.ofNat 64 (P s₀ j + t) :=
      fun t => Offset.add_add _ _ _
    by_cases ha : k < P s₀ j
    · rw [hout k (by omega), m₄, h₃.outside hp hk (by omega), h.data k hk, ite_eq_left ha]
    by_cases hb' : k < P s₀ j + n / 16 * 16
    · obtain ⟨t, rfl⟩ : ∃ t, k = P s₀ j + t := ⟨k - P s₀ j, by omega⟩
      rw [hout _ hb', m₄, ← hwinQ, h₃.data t (by omega), ite_eq_left (by simp only [Full]; omega),
        hwin, h.src hp (by omega) hk, hcnt, ksb_eq hPj (by omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, k = P s₀ j + n / 16 * 16 + i := ⟨k - (P s₀ j + n / 16 * 16), by omega⟩
      have h3 := po.data i (by omega)
      rw [Offset.add_add, Offset.add_add] at h3
      rw [h3, m₄, show P s₀ j + n / 16 * 16 + i = P s₀ j + (n / 16 * 16 + i) by omega, ← hwin,
        h₃.src hp (by omega) (by simp only [Full]; omega), hwin, h.src hp (by omega) (by omega)]
      congr 1
      have hs := h₃.stash (by omega) trivial i (by omega)
      rw [hW, show sOff n = n / 16 * 16 from rfl] at hs
      rw [hs, hcnt, ksb_eq hPj (by omega)]
  · refine (h.masks.frame h₃.frame fun r hr => kR_qR hp j r (by
      simp only [qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)).frame (rs := [eqR s₀]) ?_ ?_
    · rw [hm', ← m₄]; exact hDf
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.q_b.symm.sub_left (kR_sub s₀)

/-! ## Four blocks: the loop body -/

theorem body4_eq : body4 = .seq (.block setup4) (.seq rounds10 (.seq finish4
    (.seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 257))]) (.seq (.ite .b last (.block next4))
      (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 65))]))))) := rfl

theorem body4_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : P s₀ j + 65 ≤ eL s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa body4 s fun s' => OInv s₀ (j + 4) s' ∧ s'.cf = some (decide (eL s₀ - P s₀ (j + 4) < 65)) := by
  have hL := eL_lt s₀
  rw [body4_eq]
  refine quad4_ok hp h fun s₃ h₃ => ?_
  refine WP.seq (WP.mono (cmpi_ok s₃ .rdx (n := 257) (by decide)) fun s₄ ⟨g₄, m₄, _, r₄, w₄, c₄⟩ => ?_)
  have hrdx : s₃.gpr .rdx = BitVec.ofNat 64 (eL s₀ - P s₀ j) := by rw [h₃.keep _ (by decide), h.rdx]
  rw [hrdx, toNat_ofNat64 (by omega)] at c₄
  have h₄ := h₃.of g₄ m₄ r₄ w₄
  refine WP.seq (WP.mono (Q := fun s₅ : State => OInv s₀ (j + 4) s₅)
    (WP.ite (decide (eL s₀ - P s₀ j < 257)) (by show eval .b s₄ = _; simp only [eval, c₄])
      (fun hlt => WP.mono (last_ok hp hj (by simp only [decide_eq_true_eq] at hlt; omega) h h₄)
        fun s₅ ⟨h₅, _⟩ => h₅)
      (fun hge => WP.mono (next_ok hp (by simp only [decide_eq_false_iff_not] at hge; omega) h h₄)
        fun s₅ ⟨h₅, _⟩ => h₅))
    fun s₅ h₅ => ?_)
  refine WP.mono (cmpi_ok s₅ .rdx (n := 65) (by decide)) fun s₆ ⟨g₆, m₆, _, r₆, w₆, c₆⟩ =>
    ⟨h₅.of g₆ m₆ r₆ w₆, ?_⟩
  rw [c₆, h₅.rdx, toNat_ofNat64 (by omega)]

theorem loop4_ok {s₀ : State} (hp : TPre s₀) {s : State} (h : OInv s₀ 0 s) (hL : 65 ≤ eL s₀) :
    WP isa (.loop body4 .ae) s fun s' => ∃ j, eL s₀ - P s₀ j < 65 ∧ OInv s₀ j s' := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ j, n = eL s₀ - P s₀ j ∧ P s₀ j + 65 ≤ eL s₀ ∧ OInv s₀ j s
  have hstep : ∀ n s, Inv n s → WP isa body4 s (fun s' =>
      (eval .ae s' = some false ∧ ∃ j, eL s₀ - P s₀ j < 65 ∧ OInv s₀ j s') ∨
      (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (body4_ok hp hj hI) fun s' ⟨h', hc'⟩ => ?_
    have hP : P s₀ j < P s₀ (j + 4) := by simp only [P] at *; omega
    by_cases hl : eL s₀ - P s₀ (j + 4) < 65
    · exact .inl ⟨by simp [eval, hc', hl], j + 4, hl, h'⟩
    · exact .inr ⟨by simp [eval, hc', hl], eL s₀ - P s₀ (j + 4), by omega, j + 4, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (eL s₀ - P s₀ 0) s ⟨0, rfl, by simp [P]; omega, h⟩

/-! ## The last bytes -/

set_option simprocs false in
theorem test_ok {s₀ : State} {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      OInv s₀ j s' ∧ s'.zf = some (decide (eL s₀ - P s₀ j = 0)) := by
  have hL := eL_lt s₀
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.of rfl rfl rfl rfl, ?_⟩
  have e := Offset.ofNat_sub_ofNat_beq (x := eL s₀ - P s₀ j) (y := 0) (by omega) (by decide)
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl] at e
  rw [h.rdx, BitVec.and_self, ← e]
  simp

/-- What the end of the function leaves: `rsi` pointing at `buf`, the
destination done. -/
structure XFin (s₀ : State) (s : State) : Prop where
  rsi : s.gpr .rsi = ebp s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

/-- At most 64 bytes, but some: `vg_chacha20_xor` XORs the source's with
the keystream to the destination, and returns with `rsi` pointing at
`buf`. -/
theorem call_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hpos : P s₀ j < eL s₀) {s : State}
    (h : OInv s₀ j s) :
    WP isa (Impl.ChaCha20.X86_64.Xor.callTo "vg_chacha20_xor" Impl.ChaCha20.X86_64.Xor.xor) s (XFin s₀) := by
  have hL := eL_lt s₀
  have hle := P_le s₀ j
  have hPj : P s₀ j = 64 * j := by simp only [P] at *; omega
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.keep .rsp (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → r ≠ .r8 → (toR8 s).callEntry.gpr r = s.gpr r := fun r h h8 => by
    rw [State.callEntry_gpr _ h, RegUpd.gpr_setReg_of_ne _ _ h8]
  have h8 : (toR8 s).callEntry.gpr .r8 = edq s₀ + BitVec.ofNat 64 (P s₀ j) := by
    rw [State.callEntry_gpr _ (by decide), RegUpd.gpr_setReg_self, h.r11, h.rsi, XorBuf.sub_add_add]
  have hsp' : (toR8 s).gpr .rsp = s₀.gpr .rsp := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hsp]
  have hn : (BitVec.ofNat 64 (eL s₀ - P s₀ j)).toNat = eL s₀ - P s₀ j := toNat_ofNat_lt (by omega_arith)
  have hwr : s.wr = frT s₀ := by rw [h.wr, hp.wr]
  have hrd : s.rd = [edR s₀] := by rw [h.rd, hp.rd]
  have ts := pS_sub (s₀ := s₀) hle
  have tq := pQ_sub (s₀ := s₀) hle
  have Fce : Frame [estk s₀] s.mem (toR8 s).callEntry.mem := by
    rw [State.callEntry_mem, RegUpd.mem_setReg, hsp']
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by omega_arith) (by omega_arith))
  refine Proof.ChaCha20.wpCallTo Xor.xor_to Avx2.xor_nosp (by rw [Avx2.xor_depth]; decide)
    (rd := [pS s₀ (P s₀ j)]) (wr := [Avx2.stR (est s₀), pQ s₀ (P s₀ j), Avx2.bufR (ebp s₀)]) ?_ ?_ ?_ ?_
  · simp only [xorTo, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp) (by decide), hne _ (by decide : Reg.rsi ≠ .rsp) (by decide),
      hne _ (by decide : Reg.rdx ≠ .rsp) (by decide), hne _ (by decide : Reg.rcx ≠ .rsp) (by decide), h8, h.rdi, h.rsi,
      h.rdx, h.rcx, hsp', hn]
    refine ⟨trivial, trivial, hp.st_d.sub_right ts, hp.st_q.sub_right tq, hp.st_b, hp.d_b.sub_left ts,
      hp.q_b.sub_left tq, ?_,
      hp.stk_st.sub_left (Avx2.stk_ret s₀), (hp.stk_q.sub_left (Avx2.stk_ret s₀)).sub_right tq,
      hp.stk_b.sub_left (Avx2.stk_ret s₀), hp.stk_st.sub_left (Avx2.stk_stk s₀),
      (hp.stk_d.sub_left (Avx2.stk_stk s₀)).sub_right ts,
      (hp.stk_q.sub_left (Avx2.stk_stk s₀)).sub_right tq, hp.stk_b.sub_left (Avx2.stk_stk s₀),
      by have := hp.nowrap; bv_omega, by have := hp.nowrap_q; bv_omega⟩
    rcases hp.alias with he | hdis
    · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
    · exact .inr ((hdis.sub_left ts).sub_right tq)
  · rw [hwr, hrd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨edR s₀, by simp, P s₀ j, rfl, show P s₀ j + (eL s₀ - P s₀ j) ≤ eL s₀ by omega_arith⟩
    · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
    · exact ⟨eqR s₀, by simp, P s₀ j, rfl, show P s₀ j + (eL s₀ - P s₀ j) ≤ eL s₀ by omega_arith⟩
    · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨Avx2.stR (est s₀), by simp, 0, by simp, show 0 + 64 ≤ 64 by omega_arith⟩
    · exact ⟨eqR s₀, by simp, P s₀ j, rfl, show P s₀ j + (eL s₀ - P s₀ j) ≤ eL s₀ by omega_arith⟩
    · exact ⟨Avx2.bufR (ebp s₀), by simp, 0, by simp, show 0 + 320 ≤ 320 by omega_arith⟩
  · intro s₂ rd₂ wr₂ hcs hf _ ⟨s₃, hm₃, hg₃, hpost, hrsi₃⟩
    rw [Avx2.xor_depth, hsp] at hf
    have hce : stateAt (toR8 s).callEntry.mem (est s₀) = stateAt s.mem (est s₀) :=
      Xor.stateAt_frame Fce (by simpa using hp.stk_st.symm)
    simp only [State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp) (by decide), hne _ (by decide : Reg.rsi ≠ .rsp) (by decide),
      hne _ (by decide : Reg.rdx ≠ .rsp) (by decide), h8, h.rdi, h.rsi, h.rdx, hce, hm₃,
      h.cnt hpos] at hpost
    rw [hn] at hpost
    refine ⟨?_, fun r hr => by rw [hcs r hr]; exact h.keep r hr, fun k hk => ?_, ?_⟩
    · rw [← hg₃ .rsi (by decide), hrsi₃, State.withRegions_gpr, hne _ (by decide) (by decide), h.rcx]
    · have n_st : ¬ (Avx2.stR (est s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.st_q _ hc (in_eqR hk)
      have n_b : ¬ (Avx2.bufR (ebp s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.q_b _ (in_eqR hk) hc
      have n_sk : ¬ (estk s₀).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.stk_q _ hc (in_eqR hk)
      by_cases hk' : k < P s₀ j
      · rw [hf _ (by
          intro r hr
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact n_st
          · exact not_pQ hk' hle
          · exact n_b
          · exact n_sk), h.data k hk, ite_eq_left hk']
      · have ea : edq s₀ + BitVec.ofNat 64 k =
            edq s₀ + BitVec.ofNat 64 (P s₀ j) + BitVec.ofNat 64 (k - P s₀ j) := by
          rw [Offset.add_add, Nat.add_sub_cancel' (by omega_arith)]
        have ea' : edp s₀ + BitVec.ofNat 64 k =
            edp s₀ + BitVec.ofNat 64 (P s₀ j) + BitVec.ofNat 64 (k - P s₀ j) := by
          rw [Offset.add_add, Nat.add_sub_cancel' (by omega_arith)]
        have x := Avx2.bytes_of_bytesAt_to (length_keystream _ _) hpost (k := k - P s₀ j) (by omega_arith)
        rw [← ea, ← ea', Fce _ (by simpa using fun hc => hp.stk_d _ hc (in_dR hk)),
          h.src hp (k := k) (by omega_arith) hk, keystream_getD _ (by omega_arith)] at x
        rw [x, keystream_getD _ hk, ctr_ctr, hPj,
          show j + (k - 64 * j) / 64 = k / 64 by omega_arith, show (k - 64 * j) % 64 = k % 64 by omega_arith]
    · refine (hf.readW (r := eret s₀) (Region.contains_self _ _) ?_ (by decide)).trans ?_
      · intro r hr
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.ret_st
        · exact hp.ret_q.sub_right tq
        · exact hp.ret_b
        · exact Avx2.ret_stk s₀
      · exact h.frame.readW (Region.contains_self _ _) (ret_frT hp) (by decide)

set_option simprocs false in
theorem done_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (he : eL s₀ - P s₀ j = 0) {s : State}
    (h : OInv s₀ j s) : WP isa (.block [.mov .rsi (.reg .rcx)]) s (XFin s₀) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [State.setReg, ite_true, h.rcx], fun r hr => ?_, fun k hk => ?_, ?_⟩
  · simp only [State.setReg, (calleeSaved_ne hr).2.1, ite_false]; exact h.keep r hr
  · simp only [State.setReg]; rw [h.data k hk, ite_eq_left (by omega)]
  · simp only [State.setReg]
    exact h.frame.readW (Region.contains_self _ _) (ret_frT hp) (by decide)

theorem tail_ok {s₀ : State} (hp : TPre s₀) {j : Nat} (hj : eL s₀ - P s₀ j < 65) {s : State}
    (h : OInv s₀ j s) : WP isa tail s (XFin s₀) := by
  refine WP.seq (WP.mono (test_ok h) fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.ite (decide (eL s₀ - P s₀ j = 0)) (by simp [eval, hz]) (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    exact done_ok hp he h₁
  · simp only [decide_eq_false_iff_not] at he
    exact call_ok hp (by omega) h₁

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.X86_64.Ssse3.xor =
    .seq (.block (masks ++ Impl.ChaCha20.X86_64.XorBuf.delta ++ ([.alu .cmp .rdx (.imm 65)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop body4 .ae)) tail) := rfl

theorem correct {s₀ : State} (hp : TPre s₀) :
    WP isa Impl.ChaCha20.X86_64.Ssse3.xor s₀ fun s' =>
      (gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s') := by
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, eL s₀ - P s₀ j < 65 ∧ OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => ?_)
  · refine WP.ite (decide (eL s₀ < 65)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨0, by simp [P]; omega, h₁⟩
    · simp only [decide_eq_false_iff_not] at h
      exact loop4_ok hp h₁ (by omega)
  refine WP.mono (tail_ok hp hj h₂) fun s' hf => ⟨⟨hf.keep, hf.ret⟩, ?_, hf.rsi⟩
  exact bytesAt_xor_to (length_keystream _ _) fun k hk => by rw [hf.data k hk]

/-- `vg_chacha20_xor_ssse3` from the source to the destination, returning
with `rsi` pointing at `buf`. -/
theorem xor_to (s : State) (hs : (xorTo 16).pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86_64.Ssse3.xor s t s' ∧ abiPreserved s s' ∧ (xorTo 16).post s s' := by
  obtain ⟨t, s', he, h, hpost⟩ := correct (TPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h, hpost⟩

theorem xor_ctTo : ConstantTime isa (xorTo 16).pre (xorTo 16).pub Impl.ChaCha20.X86_64.Ssse3.xor :=
  VG.Taint.constantTime (A := taint) Xor.τ₀ (fun _ _ h₁ h₂ hp => Xor.agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.ChaCha20.X86_64.Ssse3
