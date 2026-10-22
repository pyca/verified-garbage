module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Stream
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.One
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.ChaCha20.X86_64.BlockVL

/-!
# Streaming ChaCha20 on x86-64: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of an implementation of `vg_chacha20_xor`, from their
proofs of correctness (with `WP.call`), as ChaCha20-Poly1305 makes them; and
the block function inline with AVX-512VL (`BlockVL.code`), with what the call
of `vg_chacha20_block` guarantees (`blockVL_call`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)
open VG.Proof.ChaCha20.X86_64.Xor (stateAt_frame)

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

theorem block_call {s : State} {S B : Addr} (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hsB : (below (s.gpr .rsp) 8).Disjoint ⟨B, 256⟩) (hsS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨B, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rsi = B →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockX86_64) Proof.ChaCha20.X86_64.block_correct
    (Proof.ChaCha20.X86_64.Xor.block_keeps_reg (by simp [Proof.ChaCha20.X86_64.Xor.kept]))
    (by rw [Proof.ChaCha20.X86_64.Xor.block_depth]; decide) (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi]
    exact ⟨trivial, trivial, hdj, hsB⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [Proof.ChaCha20.X86_64.Xor.block_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rsi (Proof.ChaCha20.X86_64.Xor.block_keeps_reg
      (by simp [Proof.ChaCha20.X86_64.Xor.kept])), hrsi]) ?_
    simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi,
      hrsi, hm₂] at hpost
    rwa [stateAt_frame (callEntry_frame s) (by simpa using hsS.symm)] at hpost

/-- A 16-word state in memory from its serialized bytes. -/
theorem stateAt_of_serialize {m : Mem} {p : Addr} {X : Proof.ChaCha20.CState}
    (h : ∀ k < 64, m (p + BitVec.ofNat 64 k) = (Spec.ChaCha20.serialize X).getD k 0) : stateAt m p = X := by
  apply Vector.ext; intro j hj
  simp only [stateAt, Vector.getElem_ofFn]
  refine Proof.ChaCha20.word_ext fun i hi => ?_
  rw [← Mem.readW_byte m _ hi, Offset.add_add, h _ (by omega), Proof.ChaCha20.serialize_getD _ (by omega)]
  simp only [show (4 * j + i) / 4 = j by omega, show (4 * j + i) % 4 = i by omega]

/-- `vzeroupper` keeps all but the vector registers' upper bits. -/
theorem vzu_ok (s : State) : WP isa (.block [.vop .vzeroupper]) s fun t =>
    t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The block function inline with AVX-512VL, where the 768-byte streaming
state at `S` may be written: it guarantees what the call of
`vg_chacha20_block` does (`block_call`), with the buffer at `S + 64`. -/
theorem blockVL_call {s : State} {S : Addr} (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = S + BitVec.ofNat 64 64)
    (hR : (⟨S, 768⟩ : Region) ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S + BitVec.ofNat 64 64, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      s'.gpr .rsi = S + BitVec.ofNat 64 64 →
      stateAt s'.mem (S + BitVec.ofNat 64 64) = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa Impl.ChaCha20.X86_64.BlockVL.code s Q := by
  have h₁ : WP isa (.block [.mov .r9 (.reg .rsi)]) s fun s₁ => s₁.gpr .r9 = S + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, Option.map_some,
      Option.some.injEq, exists_eq_left', ↓reduceIte, hrsi]
    exact ⟨trivial, fun r h => by simp [h], trivial, trivial, trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨r9₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = S := by rw [k₁ _ (by decide), hrdi]
  have rsi₁ : s₁.gpr .rsi = S + BitVec.ofNat 64 64 := by rw [k₁ _ (by decide), hrsi]
  have ctx : ∀ t : State, t.gpr = s₁.gpr → t.wr = s₁.wr → Avx512Tail.Ctx 0 t := by
    intro t g w
    refine ⟨fun b i n hb h hn => ?_, fun b b' hb hb' ne => ?_, by decide⟩
    · rw [w, wr₁]
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
        simp only [Avx512Tail.bsize] at h
      · simp only [Avx512Tail.regn, Avx512Tail.baseR, g, rdi₁]
        exact ⟨_, hR, Offset.contains_base S (by omega) (by omega)⟩
      · simp only [Avx512Tail.regn, Avx512Tail.baseR, g, r9₁, Offset.add_add]
        exact ⟨_, hR, Offset.contains_base S (by omega) (by omega)⟩
      · omega
    · have e : ∀ c, c < 3 → Avx512Tail.regn 0 t c =
          if c = 0 then ⟨S, 64⟩ else ⟨S + BitVec.ofNat 64 64, if c = 1 then 320 else 0⟩ := by
        intro c hc
        rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
          simp [Avx512Tail.regn, Avx512Tail.baseR, Avx512Tail.bsize, g, rdi₁, rsi₁, r9₁]
      have z : ∀ (r : Region) (a : Addr), Region.Disjoint r ⟨a, 0⟩ ∧ Region.Disjoint ⟨a, 0⟩ r :=
        fun r a => ⟨fun x _ h => by simp [Region.Contains] at h, fun x h _ => by simp [Region.Contains] at h⟩
      have d01 : Region.Disjoint ⟨S, 64⟩ ⟨S + BitVec.ofNat 64 64, 320⟩ :=
        Offset.base_disjoint S (by decide) (by omega)
      have d10 : Region.Disjoint ⟨S + BitVec.ofNat 64 64, 320⟩ ⟨S, 64⟩ :=
        Offset.disjoint_base S (by decide) (by omega)
      rw [e b hb, e b' hb']
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
        rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl <;>
        simp only [↓reduceIte, Nat.reduceEqDiff] <;>
        first | exact absurd rfl ne | exact d01 | exact d10 | exact (z _ _).1 | exact (z _ _).2
  have hc₁ := ctx s₁ rfl rfl
  refine WP.seq (WP.mono (Avx2Tail.setupOne_ok hc₁) fun s₂ ⟨hz₂, m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (Avx2Tail.roundsOne_ok hz₂ 10) fun s₃ ⟨hz₃, f₃⟩ => ?_)
  have g₃ : s₃.gpr = s₁.gpr := f₃.gpr.trans g₂
  have m₃ : s₃.mem = s₁.mem := f₃.mem.trans m₂
  have wr₃ : s₃.wr = s₁.wr := f₃.wr.trans wr₂
  have rd₃ : s₃.rd = s₁.rd := f₃.rd.trans rd₂
  refine WP.seq (WP.mono (Avx2Tail.finishOne_ok (ctx s₃ g₃ wr₃) hz₃) fun s₄ ⟨b₄, f₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono (vzu_ok s₄) fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ => ?_
  have gs : ∀ r, r ≠ .r9 → s₅.gpr r = s.gpr r := fun r h => by rw [g₅, g₄, g₃, k₁ r h]
  refine hQ s₅ (by rw [rd₅, rd₄, rd₃, rd₁]) (by rw [wr₅, wr₄, wr₃, wr₁])
    (fun r hr => gs r (by rintro rfl; simp [calleeSaved] at hr)) ?_ (by rw [gs _ (by decide), hrsi]) ?_
  · rw [m₅, ← m₁, ← m₃]
    refine f₄.sub fun r hr => ⟨_, List.mem_cons_self .., ?_⟩
    simp only [Avx512Tail.wregs, List.mem_cons, List.not_mem_nil, or_false, g₃, r9₁, rsi₁] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by decide)
    · exact Region.sub_prefix (by decide)
  · refine stateAt_of_serialize fun k hk => ?_
    have := b₄ k (by omega)
    rw [g₃, r9₁, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk] at this
    rw [m₅, this]
    simp only [Avx2Tail.plusOne, Avx512Tail.S0, g₃, m₃, rdi₁, m₁]
    rfl

/-- The block function of the last bytes, inline with AVX-512VL or by
`vg_chacha20_block` (`Stream.tailBlock`), where the 768-byte streaming state
at `S` may be written: what the call of `vg_chacha20_block` guarantees. -/
theorem tailBlock_call (x : Impl.ChaCha20.X86_64.Callee) {s : State} {S : Addr} (hrdi : s.gpr .rdi = S)
    (hrsi : s.gpr .rsi = S + BitVec.ofNat 64 64)
    (hdj : (⟨S + BitVec.ofNat 64 64, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hsB : (below (s.gpr .rsp) 8).Disjoint ⟨S + BitVec.ofNat 64 64, 256⟩)
    (hsS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨S + BitVec.ofNat 64 64, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S + BitVec.ofNat 64 64, 256⟩] s.wr) (hR : (⟨S, 768⟩ : Region) ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S + BitVec.ofNat 64 64, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      s'.gpr .rsi = S + BitVec.ofNat 64 64 →
      stateAt s'.mem (S + BitVec.ofNat 64 64) = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (Impl.ChaCha20.X86_64.Stream.tailBlock x) s Q := by
  unfold Impl.ChaCha20.X86_64.Stream.tailBlock
  split
  · exact blockVL_call hrdi hrsi hR hQ
  · exact block_call hrdi hrsi hdj hsB hsS hc hw hQ

theorem below8_24 (s : State) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) :=
  below_sub (by decide) (by decide)

/-- The precondition of the implementation `v` of `vg_chacha20_xor`, called
with 24 bytes of stack below `rsp`: 8 for its return address, and at most 16
for its calls. -/
theorem xor_pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hk := v.stack_le
  have h8 := below8_24 s
  have hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by omega) (by omega)
  simp only [Proof.ChaCha20.xorStack, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
  exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
    hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩

/-- A call of the implementation `v` of `vg_chacha20_xor` (see `xor_pre`). -/
theorem xor_call (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
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
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 := below8_24 s
  refine WP.call (k := Proof.ChaCha20.xorStack v.stack) v.ok v.nosp (by omega)
    (xor_pre v hrdi hrsi hrdx hrcx hn hSD hSB hDB hwrap hsS hsD hsB) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost, _⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by omega) (by omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_
  simp only [Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_mem,
    callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
  rw [hpost, bytesAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by omega),
    stateAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

end VG.Proof.ChaCha20.X86_64.Stream
