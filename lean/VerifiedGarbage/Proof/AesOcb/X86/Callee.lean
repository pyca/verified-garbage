import VerifiedGarbage.Proof.AesOcb.X86.Entry
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Ocb.State

/-!
# AES-OCB on x86: the calls

Untrusted: everything here is checked by Lean. Each call of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` (of any implementation
`v`), and of `vg_aes_expand_key_scratch`, in a frame of its arguments, from the
callee's contract (`WP.callWith`): what it needs of the registers it pushes
and of the regions it is given (`BCall`, AES-GCM's `KeyCall`), and what it leaves
(`BPost`, `KeyPost`), in terms of the memory before the call; and that it is
constant time (`blk_ct`, `key_ct`) by the callee's own proof, when the
arguments are the same in both runs.
-/

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 bytesAt_frame one_disj toNat_rounds CT)

/-- The implementations `v` call. -/
def callees (v : BlocksImpl) : Callees :=
  ⟨⟨v.enc.name, v.enc.code⟩, ⟨v.dec.name, v.dec.code⟩, ⟨v.expand.name, v.expand.code⟩⟩

/-- The `n` blocks at `p`, as states, over code that writes only elsewhere. -/
theorem statesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Aes.statesAt m' p n = Spec.Aes.statesAt m p n := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  simp only [Spec.Aes.stateAt]
  congr 1
  funext j
  rw [add_ofNat_assoc]
  exact hf.bytes (R := ⟨p, 16 * n⟩) hd hn (show 16 * i + j.1 < 16 * n by have := j.2; omega)

/-! ## `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` -/

abbrev blkRegs : List Reg := [.ebp, .ebx, .edx, .ecx, .eax]

theorem blkRegs_esp : Reg.esp ∉ blkRegs := by decide

/-- What a call of `vg_aes_*_blocks` needs: the key schedule at `K` for `R`
rounds, `n` blocks at `D` and working space at `S`. -/
structure BCall (s : State) (K D S : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = D
  ebx : s.gpr .ebx = BitVec.ofNat 32 n
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 24 ≤ (s.gpr .esp).toNat
  kd : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 D, 16 * n⟩
  ks : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  ds : (⟨w64 D, 16 * n⟩ : Region).Disjoint ⟨w64 S, 2048⟩
  bk : (below (s.gpr .esp) 24).Disjoint ⟨w64 K, 240⟩
  bd : (below (s.gpr .esp) 24).Disjoint ⟨w64 D, 16 * n⟩
  bs : (below (s.gpr .esp) 24).Disjoint ⟨w64 S, 2048⟩
  fK : K.toNat + 240 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨w64 K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩] s.wr

/-- What a call of a function with the contract `blocksX86 f` leaves. -/
structure BPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (K D S : BitVec 32) (R n : Nat)
    (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : Spec.Aes.statesAt s'.mem (w64 D) n =
    (Spec.Aes.statesAt s.mem (w64 D) n).map (f R (bytesAt s.mem (w64 K) (16 * (R + 1))))

abbrev blkRd (E K : BitVec 32) : List Region := [⟨w64 K, 240⟩, below E 20]
abbrev blkWr (D S : BitVec 32) (n : Nat) : List Region := [⟨w64 D, 16 * n⟩, ⟨w64 S, 2048⟩]

namespace BCall
variable {s : State} {K D S : BitVec 32} {R n : Nat} (h : BCall s K D S R n)
include h

theorem fit : 4 * blkRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fD; omega

theorem args : arg (pushed blkRegs s).callEntry 0 = K ∧ arg (pushed blkRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed blkRegs s).callEntry 2 = D ∧ arg (pushed blkRegs s).callEntry 3 = BitVec.ofNat 32 n ∧
    arg (pushed blkRegs s).callEntry 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit blkRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.ebp]

theorem sub20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 24) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 24) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 24) (k := 20) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) :
    CallPre (Proof.Aes.blocksX86 f) blkRegs (blkRd (s.gpr .esp) K) (blkWr D S n) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have eA : argAddr (pushed blkRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed blkRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.blocksX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hR, hn]
    refine ⟨trivial, trivial, h.kd, h.ks, h.ds, h.bd.sub_left h.sub20, h.bs.sub_left h.sub20,
      h.bd.sub_left h.sub4, h.bs.sub_left h.sub4, h.fK, h.fD, h.fS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a m ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a m ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a m ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a m hi
    obtain ⟨r', hr', hc'⟩ := h.writes a m hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end BCall

/-- A call of `vg_aes_*_blocks` with the contract `blocksX86 f`. -/
theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp fn.code) (stack : stackUse fn.code = 0)
    {s : State} {K D S : BitVec 32} {R n : Nat} (h : BCall s K D S R n) :
    WP isa (blocksFrame fn) s (BPost f s K D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold blocksFrame
  refine WP.callWith (rs := blkRegs) (k := Proof.Aes.blocksX86 f) ok nosp (by simp)
    blkRegs_esp (by rw [stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    (h.callPre f) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  rw [stack] at f'
  have fE := callEntry_frame h.fit blkRegs_esp
  rw [show 4 * blkRegs.length + 4 = 24 from rfl] at fE
  simp only [Proof.Aes.blocksX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hR, hn, m₂] at post
  have eK := bytesAt_frame fE (p := w64 K) (n := 16 * (R + 1))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.sub_right (Region.sub_prefix hR')).symm) (by omega)
  rw [statesAt_frame fE (one_disj h.bd) (by have := h.fD; omega), eK] at post
  refine ⟨rd', wr', cs', ?_, post⟩
  exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr

/-- Calls of `vg_aes_*_blocks` with the same arguments and stack pointer in
both runs are constant time. -/
theorem blk_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {fn : Impl.AesGcm.X86.Fn}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub fn.code)
    {I : State → Prop} {K D S E : BitVec 32} {R n : Nat}
    (h : ∀ s, I s → BCall s K D S R n ∧ s.gpr .esp = E) : CT I (blocksFrame fn) := by
  refine CT.callWith ok ct (blkRd E K) (blkWr D S n) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre f
  have p₂ := h₂.callPre f
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  simp only [Proof.Aes.blocksX86]
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `vg_aes_expand_key_scratch` -/

open VG.Proof.AesGcm.X86 (KeyCall KeyPost keyRegs keyRegs_esp keyRd keyWr) in
/-- A call of `vg_aes_expand_key_scratch`. -/
theorem key_ok (v : BlocksImpl) {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L) :
    WP isa (keyFrame (callees v)) s (KeyPost s K C S L) := by
  have hL := toNat_ofNat32 h.L_lt
  unfold keyFrame
  refine WP.callWith (rs := keyRegs) (k := Proof.Aes.expandKeyX86) v.expandOk v.expandNosp
    (by simp) keyRegs_esp (by rw [v.expandStack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega)
    h.callPre fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [v.expandStack] at f'
  have fE := callEntry_frame h.fit keyRegs_esp
  rw [show 4 * keyRegs.length + 4 = 20 from rfl] at fE
  simp only [Proof.Aes.expandKeyX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hL, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [post, bytesAt_frame fE (one_disj h.bk) (by rcases h.len with rfl | rfl | rfl <;> decide)]

open VG.Proof.AesGcm.X86 (KeyCall keyRd keyWr) in
/-- Calls of `vg_aes_expand_key_scratch` with the same arguments and stack pointer
in both runs are constant time. -/
theorem key_ct (v : BlocksImpl) {I : State → Prop} {K C S E : BitVec 32} {L : Nat}
    (h : ∀ s, I s → KeyCall s K C S L ∧ s.gpr .esp = E) : CT I (keyFrame (callees v)) := by
  refine CT.callWith v.expandOk v.expandCt (keyRd E K L) (keyWr C S) fun s₁ s₂ i₁ i₂ => ?_
  obtain ⟨h₁, e₁⟩ := h s₁ i₁
  obtain ⟨h₂, e₂⟩ := h s₂ i₂
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.AesOcb.X86
