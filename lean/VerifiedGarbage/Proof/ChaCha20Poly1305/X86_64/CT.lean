import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.X86_64.Target
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.XorBufX

/-!
# ChaCha20-Poly1305 on x86-64: the calls

Each call of a verified function, from its proof of `Verified` (with
`WP.call`): what it needs of the state it is called from, and what holds when
it returns.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-! ## Memory -/

theorem bytesAt_eq : Spec.ChaCha20.bytesAt = Spec.Poly1305.bytesAt := rfl

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem sub_off (p : Addr) {a n len : Nat} (h : a + n ≤ len) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p, len⟩ := Offset.sub_base p h

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (sub_off P (a := 24) (by lit_omega)))
      (by lit_omega)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by lit_omega)))
      (by lit_omega)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  VG.Proof.ChaCha20.X86_64.Xor.stateAt_frame hf hd

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by lit_omega) (by lit_omega))

/-! ## The callees' registers -/

theorem init_keeps : ((instrs Impl.Poly1305.X86_64.init).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem blocks_keeps : ((instrs Impl.Poly1305.X86_64.blocks).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem finalize_keeps : ((instrs Impl.Poly1305.X86_64.finalize).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem init_depth : Impl.Poly1305.X86_64.init.depth = 0 := by lit_decide
theorem blocks_depth : Impl.Poly1305.X86_64.blocks.depth = 0 := by lit_decide
theorem finalize_depth : Impl.Poly1305.X86_64.finalize.depth = 0 := by lit_decide

theorem keeps_of {c : Prog isa} {p : Instr → Bool} (h : (instrs c).all p = true) {r : Reg}
    (hr : ∀ i, p i = true → Taint.clobbers i r = false) : ∀ i ∈ instrs c, Taint.clobbers i r = false :=
  fun i hi => hr i (List.all_eq_true.mp h i hi)

theorem and_left {a b : Bool} (h : (!a && !b) = true) : a = false := by simp_all
theorem and_right {a b : Bool} (h : (!a && !b) = true) : b = false := by simp_all

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr _ h

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hsP : (below (s.gpr .rsp) 8).Disjoint ⟨P, 128⟩) (hsK : (below (s.gpr .rsp) 8).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨P, 128⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rdi = P →
      Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initX86_64) Proof.Poly1305.X86_64.init_ok
    (keeps_of init_keeps fun _ h => and_right h) (by rw [init_depth]; decide)
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.initX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi]
    exact ⟨trivial, trivial, hdj, hsP⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [init_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rdi (keeps_of init_keeps fun _ h => and_left h), hrdi]) ?_
    simp only [Proof.Poly1305.initX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi,
      hrsi, hm₂] at hpost
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using hsK.symm) (by lit_omega)] at hpost

/-! ## `vg_poly1305_blocks` -/

theorem avx2_keeps : ((instrs Impl.Poly1305.X86_64.Avx2.blocksAvx2).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem avx2_depth : Impl.Poly1305.X86_64.Avx2.blocksAvx2.depth = 1 := by lit_decide

theorem avx512_keeps : ((instrs Impl.Poly1305.X86_64.Avx512.blocksAvx512).all fun i =>
    !Taint.clobbers i .rdi && !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

theorem avx512_depth : Impl.Poly1305.X86_64.Avx512.blocksAvx512.depth = 2 := by lit_decide

/-- The stack below `rsp` that a call of `vg_poly1305_blocks` uses (24 bytes
for `vg_poly1305_blocks_avx512`, which calls `vg_poly1305_blocks_avx2`,
which calls `vg_poly1305_blocks`). -/
theorem below8_16 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by lit_omega) (by lit_omega)
theorem below8_24' (sp : Addr) : Region.Sub (below sp 8) (below sp 24) := below_sub (by lit_omega) (by lit_omega)
theorem below16_24 (sp : Addr) : Region.Sub (below sp 16) (below sp 24) := below_sub (by lit_omega) (by lit_omega)

/-- What a call of an implementation of `vg_poly1305_blocks` leaves. -/
def BlocksPost (s : State) (P p : Addr) (n : Nat) (s' : State) : Prop :=
  s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    Frame [⟨P, 128⟩, below (s.gpr .rsp) 24] s.mem s'.mem ∧ s'.gpr .rdi = P ∧
    (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) ∧
    s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

section
variable {s : State} {P p : Addr} {n : Nat} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩) (hwrap : p.toNat + 16 * n ≤ 2 ^ 64)
    (hsP : (below (s.gpr .rsp) 24).Disjoint ⟨P, 128⟩) (hsp : (below (s.gpr .rsp) 24).Disjoint ⟨p, 16 * n⟩)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩] s.wr)
include hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw

theorem scalar_call : WP isa (.call "vg_poly1305_blocks" Impl.Poly1305.X86_64.blocks) s (BlocksPost s P p n) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  have hsP8 := hsP.sub_left (below8_24' _)
  refine WP.call_mx (k := Proof.Poly1305.blocksX86_64) Proof.Poly1305.X86_64.blocks_ok
    (keeps_of blocks_keeps fun _ h => and_right h) (by rw [blocks_depth]; decide)
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hn']
    exact ⟨trivial, trivial, hdj, hsP8, hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [blocks_depth] at hf
    refine ⟨hrd, hwr, hcs, hf.sub fun r hr => ?_,
      by rw [hkeep .rdi (keeps_of blocks_keeps fun _ h => and_left h), hrdi], fun key msg hr => ?_, hmx⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, below8_24' _⟩
    simp only [Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    have h := hpost key msg (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP8.symm))
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using (hsp.sub_left (below8_24' _)).symm)
      (by lit_omega)] at h

theorem avx2_call :
    WP isa (.call "vg_poly1305_blocks_avx2" Impl.Poly1305.X86_64.Avx2.blocksAvx2) s (BlocksPost s P p n) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  have hsP8 := hsP.sub_left (below8_24' _)
  refine WP.call_mx (k := Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64)
    Proof.Poly1305.X86_64.Avx2.blocksAvx2_ok
    (keeps_of avx2_keeps fun _ h => and_right h) (by rw [avx2_depth]; decide)
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hn']
    exact ⟨trivial, trivial, hdj, hsP8, (hsP.sub_left (below16_24 _)).sub_left (below_callee _ 8),
      (hsp.sub_left (below16_24 _)).sub_left (below_callee _ 8), hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [avx2_depth] at hf
    refine ⟨hrd, hwr, hcs, hf.sub fun r hr => ?_,
      by rw [hkeep .rdi (keeps_of avx2_keeps fun _ h => and_left h), hrdi], fun key msg hr => ?_, hmx⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, below16_24 _⟩
    simp only [Proof.Poly1305.X86_64.Avx2.blocksAvx2X86_64, Proof.Poly1305.blocksX86_64,
      State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    have h := hpost key msg (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP8.symm))
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using (hsp.sub_left (below8_24' _)).symm)
      (by lit_omega)] at h

theorem avx512_call :
    WP isa (.call "vg_poly1305_blocks_avx512" Impl.Poly1305.X86_64.Avx512.blocksAvx512) s (BlocksPost s P p n) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by lit_omega)
  have hsP8 := hsP.sub_left (below8_24' _)
  refine WP.call_mx (k := Proof.Poly1305.X86_64.Avx512.blocksAvx512X86_64)
    Proof.Poly1305.X86_64.Avx512.blocksAvx512_ok
    (keeps_of avx512_keeps fun _ h => and_right h) (by rw [avx512_depth]; decide)
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.X86_64.Avx512.blocksAvx512X86_64, Proof.Poly1305.blocksStack,
      State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hn']
    exact ⟨trivial, trivial, hdj, hsP8, hsP.sub_left (below_callee _ 16),
      hsp.sub_left (below_callee _ 16), hwrap⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩ hmx
    rw [avx512_depth] at hf
    refine ⟨hrd, hwr, hcs, hf,
      by rw [hkeep .rdi (keeps_of avx512_keeps fun _ h => and_left h), hrdi], fun key msg hr => ?_, hmx⟩
    simp only [Proof.Poly1305.X86_64.Avx512.blocksAvx512X86_64, Proof.Poly1305.blocksStack,
      Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    have h := hpost key msg (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP8.symm))
    rwa [bytesAt_frame (callEntry_frame s) (by simpa using (hsp.sub_left (below8_24' _)).symm)
      (by lit_omega)] at h

/-- A call of the implementation `b` of `vg_poly1305_blocks`. -/
theorem blocks_call (b : Impl.Poly1305.X86_64.Blocks) : WP isa (.call b.name b.code) s (BlocksPost s P p n) := by
  cases b
  · exact scalar_call hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw
  · exact avx2_call hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw
  · exact avx512_call hrdi hrsi hrdx hn hdj hwrap hsP hsp hc hw

end

/-! ## `vg_poly1305_finalize_scratch` -/

theorem finalize_call {s : State} {P O : Addr} (hrdi : s.gpr .rdi = P) (hrsi : s.gpr .rsi = 0)
    (hrdx : s.gpr .rdx = O) (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩)
    (hsP : (below (s.gpr .rsp) 8).Disjoint ⟨P, 128⟩) (hsO : (below (s.gpr .rsp) 8).Disjoint ⟨O, 16⟩)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨P, 128⟩, ⟨O, 16⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rdi = P → s'.gpr .rcx = O →
      (∀ key msg, Repr s.mem P key msg → bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.X86_64.finalize) s Q := by
  have k1 : ∀ i ∈ instrs Impl.Poly1305.X86_64.finalize, Taint.clobbers i .rdi = false :=
    keeps_of finalize_keeps fun _ h => and_left h
  have k3 : ∀ i ∈ instrs Impl.Poly1305.X86_64.finalize, Taint.clobbers i .rsp = false :=
    keeps_of finalize_keeps fun _ h => and_right h
  refine WP.call (k := Proof.Poly1305.finalizeX86_64) Proof.Poly1305.X86_64.finalize_ok
    k3 (by rw [finalize_depth]; decide) (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.finalizeX86_64, State.withRegions_gpr, State.withRegions_wr,
      State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrdx]
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, hPO, hsP, hsO⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hrcx₂, hpost⟩
    rw [finalize_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rdi k1, hrdi]) ?_ fun key msg hr => ?_
    · rw [← hg₂ .rcx (by decide), hrcx₂, State.withRegions_gpr, callEntry_gpr' s (by decide), hrdx]
    simp only [State.withRegions_gpr, State.withRegions_mem, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi,
      hrsi, hrdx, hm₂] at hpost
    refine hpost key msg (Proof.Poly1305.Repr.buffered
      (Repr.frame (callEntry_frame s) (h := hr) (by simpa using hsP.symm))) ?_
    rw [show (0 : BitVec 64).toNat = 0 from rfl, hr.1]

/-! ## `vg_chacha20_block` -/

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

/-! ## `vg_chacha20_xor` -/

theorem below8_24 (s : State) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) :=
  below_sub (by lit_omega) (by lit_omega)

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
    exact Offset.sub_below _ (by lit_omega) (by lit_omega)
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
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem → s'.gpr .rsi = B →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem D n) (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 := below8_24 s
  refine WP.call (k := Proof.ChaCha20.xorStack v.stack) v.ok v.nosp (by lit_omega)
    (xor_pre v hrdi hrsi hrdx hrcx hn hSD hSB hDB hwrap hsS hsD hsB) hc hw ?_
  intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, hg₂, hpost, hrsi₂⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by lit_omega) (by lit_omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_ ?_
  · rw [← hg₂ .rsi (by decide), hrsi₂, State.withRegions_gpr, callEntry_gpr' s (by decide), hrcx]
  · simp only [Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
    rw [hpost, bytesAt_eq, bytesAt_frame (callEntry_frame s) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by lit_omega),
      stateAt_frame (callEntry_frame s) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: the entry state, regions and invariant
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.X86_64 in
/-- The precondition of both functions, `(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, data = r8, len = r9, tag = [rsp + 8], work = [rsp + 16])`:
`work` (1696 bytes) and `data` may be read and written, `key`, `nonce`, `aad`
and the stack arguments read, and `tag` written if `enc` (`seal`) and read if
not (`open`); no writable one overlaps another, the return address or the 24
bytes of stack below it, where the calls store their return addresses (16 for
that of `vg_chacha20_xor` and the calls of any of its implementations, see
`XorImpl`); nothing wraps around the end of the address space. -/
def preX86_64 (enc : Bool) (s : X86_64.State) : Prop :=
  let key : Region := ⟨s.gpr .rdi, 32⟩
  let nonce : Region := ⟨s.gpr .rsi, 12⟩
  let aad : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let work : Region := ⟨stackArg s 1, 1696⟩
  let args : Region := ⟨stackArgAddr s 0, 16⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
  s.rd = (if enc then [key, nonce, aad, args] else [key, nonce, aad, tag, args]) ∧
  s.wr = (if enc then [data, tag, work] else [data, work]) ∧
  work.Disjoint key ∧ work.Disjoint nonce ∧ work.Disjoint aad ∧ work.Disjoint data ∧
  work.Disjoint tag ∧ work.Disjoint args ∧
  data.Disjoint key ∧ data.Disjoint nonce ∧ data.Disjoint aad ∧ data.Disjoint tag ∧
  data.Disjoint args ∧
  ret.Disjoint work ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
  stack.Disjoint work ∧ stack.Disjoint key ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧
  stack.Disjoint data ∧ stack.Disjoint tag ∧
  (stackArg s 1).toNat + 1696 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
  (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧
  (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64

open VG.X86_64 in
def pubX86_64 (s₁ s₂ : X86_64.State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
  s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
  s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

open VG.X86_64 in
/-- `vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, data, len, tag, work)`. -/
def sealX86_64 : Contract X86_64.isa where
  pre := preX86_64 true
  post s s' :=
    encrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat, bytesAt s'.mem (stackArg s 0) 16)
  pub := pubX86_64

open VG.X86_64 in
/-- `vg_chacha20_poly1305_open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`. -/
def openX86_64 : Contract X86_64.isa where
  pre := preX86_64 false
  post s s' :=
    match decrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (bytesAt s.mem (stackArg s 0) 16) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub := pubX86_64

end VG.Proof.ChaCha20Poly1305

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by
  simp only [off]; congr 1

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem signExtend_of_msb {v : BitVec 32} (h : v.msb = false) :
    v.signExtend 64 = BitVec.ofNat 64 v.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false h]
  apply BitVec.eq_of_toNat_eq
  simp

theorem se_ofNat {k : Nat} (h : k < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := by
  rw [signExtend_of_msb (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by lit_omega)]; simp; omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by lit_omega)]

/-! ## The entry state -/

section
variable (s₀ : State)
/-- The working space (the context), `[rsp + 16]`. -/
abbrev cx : Addr := stackArg s₀ 1
/-- The tag, `[rsp + 8]`. -/
abbrev tp : Addr := stackArg s₀ 0
abbrev kp : Addr := s₀.gpr .rdi
abbrev np : Addr := s₀.gpr .rsi
abbrev ad : Addr := s₀.gpr .rdx
abbrev AL : Nat := (s₀.gpr .rcx).toNat
abbrev dp : Addr := s₀.gpr .r8
abbrev L : Nat := (s₀.gpr .r9).toNat
/-- The key, the nonce, the additional data, the data and the tag on entry. -/
abbrev K : List Byte := bytesAt s₀.mem (kp s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (np s₀) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (tp s₀) 16
/-- The one-time Poly1305 key. -/
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
abbrev ctxR : Region := ⟨cx s₀, 1696⟩
abbrev kR : Region := ⟨kp s₀, 32⟩
abbrev nR : Region := ⟨np s₀, 12⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev tR : Region := ⟨tp s₀, 16⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 24
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

/-- What the proof uses of the precondition; `enc` for `seal`. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = if enc then [kR s₀, nR s₀, aR s₀, argR s₀] else [kR s₀, nR s₀, aR s₀, tR s₀, argR s₀]
  wr : s₀.wr = if enc then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀]
  c_k : (ctxR s₀).Disjoint (kR s₀)
  c_n : (ctxR s₀).Disjoint (nR s₀)
  c_a : (ctxR s₀).Disjoint (aR s₀)
  c_d : (ctxR s₀).Disjoint (dR s₀)
  c_t : (ctxR s₀).Disjoint (tR s₀)
  c_g : (ctxR s₀).Disjoint (argR s₀)
  d_k : (dR s₀).Disjoint (kR s₀)
  d_n : (dR s₀).Disjoint (nR s₀)
  d_a : (dR s₀).Disjoint (aR s₀)
  d_t : (dR s₀).Disjoint (tR s₀)
  d_g : (dR s₀).Disjoint (argR s₀)
  ret_c : (retR s₀).Disjoint (ctxR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_t : (retR s₀).Disjoint (tR s₀)
  stk_c : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (ctxR s₀)
  stk_k : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (kR s₀)
  stk_n : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (nR s₀)
  stk_a : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (aR s₀)
  stk_d : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (dR s₀)
  stk_t : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (tR s₀)
  wrap_c : (cx s₀).toNat + 1696 ≤ 2 ^ 64
  wrap_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  wrap_t : (tp s₀).toNat + 16 ≤ 2 ^ 64
  wrap_k : (kp s₀).toNat + 32 ≤ 2 ^ 64
  wrap_n : (np s₀).toNat + 12 ≤ 2 ^ 64

theorem APre.of {enc : Bool} (s₀ : State) (h : preX86_64 enc s₀) : APre enc s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩

theorem APre.a_d {enc : Bool} {s₀ : State} (hp : APre enc s₀) : (aR s₀).Disjoint (dR s₀) := hp.d_a.symm

theorem stkR_eq (s₀ : State) : stkR s₀ = ⟨s₀.gpr .rsp - 24, 24⟩ := rfl

variable {e : Bool}

theorem APre.ctx_wr {s₀ : State} (hp : APre e s₀) : ctxR s₀ ∈ s₀.wr := by
  rw [hp.wr]; cases e <;> simp

theorem APre.d_wr {s₀ : State} (hp : APre e s₀) : dR s₀ ∈ s₀.wr := by
  rw [hp.wr]; cases e <;> simp

theorem APre.a_rd {s₀ : State} (hp : APre e s₀) : aR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.k_rd {s₀ : State} (hp : APre e s₀) : kR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.n_rd {s₀ : State} (hp : APre e s₀) : nR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.g_rd {s₀ : State} (hp : APre e s₀) : argR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.t_wr {s₀ : State} (hp : APre true s₀) : tR s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem APre.t_rd {s₀ : State} (hp : APre false s₀) : tR s₀ ∈ s₀.rd := by
  rw [hp.rd]; simp

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 1696) : Region.Sub (sub s₀ k n) (ctxR s₀) := by
  rw [sub, off_eq]; exact sub_off _ h

theorem sub_sub (s₀ : State) {a m k n : Nat} (h₁ : a ≤ k) (h₂ : k + n ≤ a + m) (_h₃ : a + m ≤ 1696) :
    Region.Sub (sub s₀ k n) (sub s₀ a m) := by
  simp only [sub, off_eq]; exact Offset.sub (cx s₀) h₁ h₂

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 1696)
    (hb : b + m ≤ 1696) : (sub s₀ a n).Disjoint (sub s₀ b m) := by
  simp only [sub, off_eq]; exact Offset.disjoint (cx s₀) h (by lit_omega) (by lit_omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 1696) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := by
  simp only [sub, off_eq]; exact Offset.contains (cx s₀) h₁ h₂ (by lit_omega)

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 1696) : (ctxR s₀).Contains (off (cx s₀) a) w := by
  rw [off_eq]; exact Offset.contains_base (cx s₀) h (by lit_omega)

theorem APre.in_ctx {s₀ : State} (hp : APre e s₀) {a w : Nat} (h : a + w ≤ 1696) :
    InRegions s₀.wr (off (cx s₀) a) w := ⟨ctxR s₀, hp.ctx_wr, contains_ctx s₀ h⟩

theorem APre.in_ctx' {s₀ : State} (hp : APre e s₀) {a w : Nat} (h : a + w ≤ 1696) :
    InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w := ⟨ctxR s₀, by simp [hp.ctx_wr], contains_ctx s₀ h⟩

theorem APre.off_toNat {s₀ : State} (hp : APre e s₀) {k : Nat} (hk : k < 1696) :
    (off (cx s₀) k).toNat = (cx s₀).toNat + k := by
  have := hp.wrap_c
  rw [off_eq, BitVec.toNat_add, toNat_ofNat_lt (by lit_omega), Nat.mod_eq_of_lt (by lit_omega)]

/-- The stack below `rsp` that the calls use. -/
theorem below8_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) := below_sub (by lit_omega) (by lit_omega)

theorem below16_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 16) (stkR s₀) :=
  below_sub (by lit_omega) (by lit_omega)

theorem APre.stk_sub {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 1696) :
    (stkR s₀).Disjoint (sub s₀ k n) := hp.stk_c.sub_right (sub_ctx s₀ h)

theorem APre.below8_sub {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 1696) :
    (below (s₀.gpr .rsp) 8).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (below8_stk s₀)

theorem APre.below16_sub {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 1696) :
    (below (s₀.gpr .rsp) 16).Disjoint (sub s₀ k n) := (hp.stk_sub h).sub_left (below16_stk s₀)

/-! ## The saved registers and the invariant -/

/-- Our caller's `rbx, rbp, r13, r14, r15, r12`, saved in `ctx[0, 48)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (off (cx s₀) 0) 64 = s₀.gpr .rbx ∧ m.readW (off (cx s₀) 8) 64 = s₀.gpr .rbp ∧
  m.readW (off (cx s₀) 16) 64 = s₀.gpr .r13 ∧ m.readW (off (cx s₀) 24) 64 = s₀.gpr .r14 ∧
  m.readW (off (cx s₀) 32) 64 = s₀.gpr .r15 ∧ m.readW (off (cx s₀) 40) 64 = s₀.gpr .r12

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ 0 48).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 0 ≤ d → d + 8 ≤ 48 → (sub s₀ 0 48).Contains (off (cx s₀) d) (64 / 8) :=
    fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by lit_omega)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨by rw [hf.readW (c 0 (Nat.le_refl _) (by lit_omega)) hd (by decide), h1],
    by rw [hf.readW (c 8 (by lit_omega) (by lit_omega)) hd (by decide), h2],
    by rw [hf.readW (c 16 (by lit_omega) (by lit_omega)) hd (by decide), h3],
    by rw [hf.readW (c 24 (by lit_omega) (by lit_omega)) hd (by decide), h4],
    by rw [hf.readW (c 32 (by lit_omega) (by lit_omega)) hd (by decide), h5],
    by rw [hf.readW (c 40 (by lit_omega) (by lit_omega)) hd (by decide), h6]⟩

/-- The working space: all of `ctx`, `ctx[0, 1696)`. -/
abbrev workR (s₀ : State) : Region := sub s₀ 0 1696

/-- What holds between the parts of the code. -/
structure Inv (s₀ : State) (s : State) : Prop where
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r12 : s.gpr .r12 = tp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem s.mem

/-! ## Pointers -/

set_option simprocs false in
theorem ptr_ok (d r : Reg) {k : Nat} (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (ptr d r k)) s fun s' =>
      s'.gpr d = off (s.gpr r) k ∧ (∀ q, q ≠ d → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [and_self, ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se_ofNat hk]
  exact ⟨by rw [off_eq], fun q hq => by simp [hq], trivial⟩

set_option simprocs false in
theorem anchor_ok (r : Reg) {k : Nat} (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (anchor r k)) s fun s' =>
      s'.gpr .r15 = s.gpr r - BitVec.ofNat 64 k ∧ (∀ q, q ≠ .r15 → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [and_self, anchor, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se_ofNat hk]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem off_sub (p : Addr) (k : Nat) : off p k - BitVec.ofNat 64 k = p := by
  rw [off_eq]; exact BitVec.add_sub_cancel _ _

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Covering the callees' regions -/

theorem covers_sub {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 1696) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, k, by rw [hrk]; simp [off_eq], hk⟩

/-! ## The entry -/

/-- The state after `entry`: `work` in `rax` and `tag` in `r11`. -/
def entryS (s₀ : State) : State := (s₀.setReg .rax (cx s₀)).setReg .r11 (tp s₀)

theorem entry_run {s₀ : State} (hp : APre e s₀) :
    execBlock isa entry s₀ = some (entryS s₀,
      [.addr (off (s₀.gpr .rsp) 16), .addr (off (s₀.gpr .rsp) 8)]) := by
  have hg : ∀ k, k + 8 ≤ 16 → InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .rsp) (8 + k)) 8 := by
    intro k hk
    refine ⟨argR s₀, by simp [hp.g_rd], ?_⟩
    rw [off_eq, show s₀.gpr .rsp + BitVec.ofNat 64 (8 + k) = stackArgAddr s₀ 0 + BitVec.ofNat 64 k by
      simp only [stackArgAddr, BitVec.ofNat_add, BitVec.add_assoc]]
    exact Offset.contains_base _ hk (by lit_omega)
  have h16 := hg 8 (by omega)
  have h8 := hg 0 (by omega)
  simp only [show 8 + 8 = 16 from rfl, show 8 + 0 = 8 from rfl] at h16 h8
  have e16 : s₀.mem.readW (off (s₀.gpr .rsp) 16) 64 = cx s₀ := by
    simp only [cx, stackArg, stackArgAddr, off_eq]
  have e8 : s₀.mem.readW (off (s₀.gpr .rsp) 8) 64 = tp s₀ := by
    simp only [tp, stackArg, stackArgAddr, off_eq]
  have hsp : (s₀.setReg .rax (cx s₀)).gpr .rsp = s₀.gpr .rsp := RegUpd.gpr_setReg_of_ne _ _ (by decide)
  simp only [entry, execBlock, isa, exec, readSrc, State.load64, ea_at, h16, ite_true, Option.map_some,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, hsp, h8, e16, e8, addrs, srcAddrs, entryS]
  rfl

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: the prologue

Saving the registers, the ChaCha20 state for counter 0, the one-time key and
the Poly1305 state for it.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-! ## Saving the registers -/

theorem saveMoves_eq : save ++ moves =
    [.store (at_ .rax 0) .rbx, .store (at_ .rax 8) .rbp, .store (at_ .rax 16) .r13,
     .store (at_ .rax 24) .r14, .store (at_ .rax 32) .r15, .store (at_ .rax 40) .r12,
     .mov .r15 (.reg .rax), .mov .r12 (.reg .r11), .mov .rbx (.reg .rdx), .mov .rbp (.reg .rcx),
     .mov .r14 (.reg .r8), .mov .r13 (.reg .r9)] := rfl

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86_64.off_sep p hd he (by lit_omega) (by lit_omega) h) (by decide)

set_option simprocs false in
theorem saveMoves_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves)) (entryS s₀) fun s =>
      s.gpr .r15 = cx s₀ ∧ s.gpr .r12 = tp s₀ ∧ s.gpr .rbx = ad s₀ ∧ s.gpr .rbp = s₀.gpr .rcx ∧
      s.gpr .r14 = dp s₀ ∧ s.gpr .r13 = s₀.gpr .r9 ∧
      (∀ r, r ≠ .r15 → r ≠ .r12 → r ≠ .rbx → r ≠ .rbp → r ≠ .r14 → r ≠ .r13 → r ≠ .rax → r ≠ .r11 →
        s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      Frame [sub s₀ 0 48] s₀.mem s.mem ∧ Saved s₀ s.mem := by
  have o0 := hp.in_ctx (a := 0) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 8) (w := 8) (by lit_omega)
  have o2 := hp.in_ctx (a := 16) (w := 8) (by lit_omega)
  have o3 := hp.in_ctx (a := 24) (w := 8) (by lit_omega)
  have o4 := hp.in_ctx (a := 32) (w := 8) (by lit_omega)
  have o5 := hp.in_ctx (a := 40) (w := 8) (by lit_omega)
  simp only [off] at o0 o1 o2 o3 o4 o5
  apply WP.of_runBlock
  rw [saveMoves_eq]
  simp (config := {decide := true}) only [entryS, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.store64, State.setReg, o0, o1, o2, o3, o4, o5, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial,
    fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => by simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈], trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 0 ≤ d → d + 8 ≤ 48 → (sub s₀ 0 48).Contains (off (cx s₀) d) (64 / 8) :=
      fun d h₁ h₂ => contains_sub s₀ h₁ h₂ (by lit_omega)
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (Nat.le_refl _) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 8 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 16 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 24 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 32 (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (c 40 (by lit_omega) (by lit_omega))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) only [off, Mem.readW_writeW_self64, readW64_off]

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m`, the key at `kp` and the nonce
at `np`. -/
def wordOf (m : Mem) (kp np : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0
  else if k < 12 then m.readW (off kp (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off np (4 * (k - 13))) 32

/-- The context may be read and written, and the key and the nonce read. -/
def CtxOk (c kp np : Addr) (s : State) : Prop :=
  (∀ a w, a + w ≤ 1696 → InRegions (s.rd ++ s.wr) (off c a) w ∧ InRegions s.wr (off c a) w) ∧
  (∀ a w, a + w ≤ 32 → InRegions (s.rd ++ s.wr) (off kp a) w) ∧
  (∀ a w, a + w ≤ 12 → InRegions (s.rd ++ s.wr) (off np a) w)

/-- Quadword `j` of the ChaCha20 state: words `2j` and `2j + 1`. -/
def qOf (m : Mem) (kp np : Addr) (j : Nat) : BitVec 64 := wordOf m kp np (2 * j + 1) ++ wordOf m kp np (2 * j)

/-- A quadword is its two words. -/
theorem split64 (x : BitVec 64) : x = x.extractLsb' 32 32 ++ x.extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 32
  · simp [h]
  · simp [h, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

/-- Bits `8k` to `8(k + n)` of a read are a read at `a + k`. -/
theorem extract_readW (m : Mem) (a : Addr) {w k n : Nat} (h : 8 * (k + n) ≤ w) :
    (m.readW a w).extractLsb' (8 * k) (8 * n) = m.readW (a + BitVec.ofNat 64 k) (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [decide_eq_true (by omega), Bool.true_and, VG.X86_64.getLsbD_read _ _ (by omega),
    VG.X86_64.getLsbD_read _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show (8 * k + i) / 8 = k + i / 8 by omega, show (8 * k + i) % 8 = i % 8 by omega]

/-- A quadword read is its two words. -/
theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  have e₁ : (m.readW a 64).extractLsb' 32 32 = m.readW (a + BitVec.ofNat 64 4) 32 :=
    extract_readW m a (w := 64) (k := 4) (n := 4) (by omega)
  have e₀ : (m.readW a 64).extractLsb' 0 32 = m.readW a 32 := by
    have := extract_readW m a (w := 64) (k := 0) (n := 4) (by omega)
    simpa using this
  rw [← e₁, ← e₀]
  exact split64 _

/-- The words of a quadword written. -/
theorem readW_qword (m : Mem) (a : Addr) (hi lo : BitVec 32) :
    (m.writeW a (hi ++ lo)).readW a 32 = lo ∧
      (m.writeW a (hi ++ lo)).readW (a + BitVec.ofNat 64 4) 32 = hi := by
  have h₀ := VG.X86_64.readW_writeW_inside m a (hi ++ lo) (k := 0) (n := 4) (by omega) (by omega)
  have h₁ := VG.X86_64.readW_writeW_inside m a (hi ++ lo) (k := 4) (n := 4) (by omega) (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at h₀
  refine ⟨h₀.trans ?_, h₁.trans ?_⟩
  · apply BitVec.eq_of_getLsbD_eq; intro i hi'
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [show i < 32 by omega]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi'
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [show i < 32 by omega, show ¬ (32 + i < 32) by omega, show 32 + i - 32 = i by omega]

theorem qOf_c0 (m : Mem) (kp np : Addr) : qOf m kp np 0 = 3684054920433006693 := by
  simp only [qOf, wordOf, show 2 * 0 + 1 < 4 from by decide, show 2 * 0 < 4 from by decide, ite_true]
  decide

theorem qOf_c1 (m : Mem) (kp np : Addr) : qOf m kp np 1 = 7719281312240119090 := by
  simp only [qOf, wordOf, show 2 * 1 + 1 < 4 from by decide, show 2 * 1 < 4 from by decide, ite_true]
  decide

theorem qOf_key (m : Mem) (kp np : Addr) {j : Nat} (h₁ : 2 ≤ j) (h₂ : j < 6) :
    qOf m kp np j = m.readW (off kp (8 * (j - 2))) 64 := by
  have a₁ : ¬ 2 * j + 1 < 4 := by omega
  have a₂ : ¬ 2 * j < 4 := by omega
  have b₁ : 2 * j + 1 < 12 := by omega
  have b₂ : 2 * j < 12 := by omega
  rw [readW64_split]
  simp only [qOf, wordOf, a₁, a₂, b₁, b₂, ite_true, ite_false]
  rw [show 4 * (2 * j + 1 - 4) = 8 * (j - 2) + 4 by omega,
    show 4 * (2 * j - 4) = 8 * (j - 2) by omega, off_eq, off_eq, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem qOf_n6 (m : Mem) (kp np : Addr) : qOf m kp np 6 = m.readW (off np 0) 32 ++ (0 : BitVec 32) := by
  simp only [qOf, wordOf, show ¬ 2 * 6 + 1 < 4 from by decide, show ¬ 2 * 6 < 4 from by decide,
    show ¬ 2 * 6 + 1 < 12 from by decide, show ¬ 2 * 6 + 1 = 12 from by decide,
    show ¬ 2 * 6 < 12 from by decide, show 2 * 6 = 12 from rfl, ite_true, ite_false,
    show 4 * (2 * 6 + 1 - 13) = 0 from rfl]

theorem qOf_n7 (m : Mem) (kp np : Addr) : qOf m kp np 7 = m.readW (off np 4) 64 := by
  rw [readW64_split]
  simp only [qOf, wordOf, show ¬ 2 * 7 + 1 < 4 from by decide, show ¬ 2 * 7 < 4 from by decide,
    show ¬ 2 * 7 + 1 < 12 from by decide, show ¬ 2 * 7 + 1 = 12 from by decide,
    show ¬ 2 * 7 < 12 from by decide, show ¬ 2 * 7 = 12 from by decide, ite_false]
  rw [show 4 * (2 * 7 + 1 - 13) = 4 + 4 from rfl, show 4 * (2 * 7 - 13) = 4 from rfl, off_eq, off_eq,
    BitVec.add_assoc, ← BitVec.ofNat_add]

set_option simprocs false in
theorem stQ_ok {c kp np : Addr} {o j : Nat} (ho : o + 64 ≤ 1696) (hj : j < 8) {s : State} (hr15 : s.gpr .r15 = c)
    (hrdi : s.gpr .rdi = kp) (hrsi : s.gpr .rsi = np) (hc : CtxOk c kp np s) :
    WP isa (.block (stQ o j)) s fun s' =>
      s'.mem = s.mem.writeW (off c (o + 8 * j)) (qOf s.mem kp np j) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := (hc.1 (o + 8 * j) 8 (by lit_omega)).2
  simp only [off] at o
  unfold stQ stQSrc
  split_ifs with h₁ h₂ h₃ h₄
  · subst h₁
    apply WP.of_runBlock
    simp only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      State.store64, State.setReg, show (Reg.r15 = Reg.rax) = False from by decide, hr15, o, ite_true,
      ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨by rw [qOf_c0], fun r hr => by simp [hr], trivial, trivial⟩
  · subst h₂
    apply WP.of_runBlock
    simp only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      State.store64, State.setReg, show (Reg.r15 = Reg.rax) = False from by decide, hr15, o, ite_true,
      ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨by rw [qOf_c1], fun r hr => by simp [hr], trivial, trivial⟩
  · have i := hc.2.1 (8 * (j - 2)) 8 (by lit_omega)
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc, State.load64, State.store64, State.setReg, hr15, hrdi, o, i, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨by rw [qOf_key _ _ _ (by omega) (by omega)], fun r hr => by simp [hr], trivial⟩
  · subst h₄
    have i := hc.2.2 0 4 (by lit_omega)
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc32, execShift, State.load32, State.store64, State.setReg, State.setReg32, State.setFlags, hr15,
      hrsi, o, i, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => by simp [hr], trivial⟩
    refine congrArg _ ?_
    rw [qOf_n6]
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
    by_cases h : k < 32
    · simp [h, hk]
    · simp [h, hk]; omega
  · have hj7 : j = 7 := by omega
    subst hj7
    have i := hc.2.2 4 8 (by lit_omega)
    simp only [off] at i
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
      readSrc, State.load64, State.store64, State.setReg, hr15, hrsi, o, i, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left']
    exact ⟨by rw [qOf_n7], fun r hr => by simp [hr], trivial⟩

theorem readW32_off (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 32 = m.readW (off p d) 32 :=
  VG.Proof.ChaCha20.X86_64.readW_writeW_off m p v (Or.inl rfl) hd he h

/-- A word `[a, a + 4)` of a buffer `⟨p, n⟩` apart from the frame. -/
theorem readW_frame_buf {c p : Addr} {m m' : Mem} {o k n : Nat} (hf : Frame [⟨off c o, k⟩] m m')
    (hd : (⟨off c o, k⟩ : Region).Disjoint ⟨p, n⟩) {a : Nat} (ha : a + 4 ≤ n) :
    m'.readW (off p a) 32 = m.readW (off p a) 32 := by
  refine hf.readW (r := ⟨off p a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq, off_eq]
  exact (hd.sub_right (Offset.sub_base p (d := a) (n := 4) ha)).symm

theorem wordOf_frame {c kp np : Addr} {m m' : Mem} {o n : Nat} (hf : Frame [⟨off c o, n⟩] m m')
    (hk : (⟨off c o, n⟩ : Region).Disjoint ⟨kp, 32⟩) (hn : (⟨off c o, n⟩ : Region).Disjoint ⟨np, 12⟩)
    {k : Nat} (hk16 : k < 16) : wordOf m' kp np k = wordOf m kp np k := by
  unfold wordOf
  split_ifs <;> [rfl; exact readW_frame_buf hf hk (by lit_omega); rfl;
    exact readW_frame_buf hf hn (by lit_omega)]

theorem initStateQ_step (o j : Nat) :
    (List.range (j + 1)).flatMap (stQ o) = (List.range j).flatMap (stQ o) ++ stQ o j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` quadwords of the ChaCha20 state. -/
theorem initStateQ_ok' {c kp np : Addr} {o j : Nat} (ho : o + 64 ≤ 1696) (hj : j ≤ 8) {s : State}
    (hr15 : s.gpr .r15 = c) (hrdi : s.gpr .rdi = kp) (hrsi : s.gpr .rsi = np) (hc : CtxOk c kp np s)
    (hk : (⟨off c o, 64⟩ : Region).Disjoint ⟨kp, 32⟩) (hn : (⟨off c o, 64⟩ : Region).Disjoint ⟨np, 12⟩) :
    WP isa (.block ((List.range j).flatMap (stQ o))) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨off c o, 8 * j⟩] s.mem s'.mem ∧
      ∀ i < 2 * j, s'.mem.readW (off c (o + 4 * i)) 32 = wordOf s.mem kp np i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by lit_omega)⟩
  | succ j ih =>
    rw [initStateQ_step]
    refine WP.block_append (WP.mono (ih (by lit_omega)) fun s₁ ⟨g₁, rd₁, wr₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk c kp np s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    have hsub : Region.Sub ⟨off c o, 8 * j⟩ ⟨off c o, 64⟩ := Region.sub_prefix (by lit_omega)
    refine WP.mono (stQ_ok ho (by lit_omega) (by rw [g₁ _ (by decide), hr15]) (by rw [g₁ _ (by decide), hrdi])
      (by rw [g₁ _ (by decide), hrsi]) hc₁) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by lit_omega)
      · simp only [off_eq]
        exact Offset.contains c (by lit_omega) (by lit_omega) (by lit_omega)
    · have hq : qOf s₁.mem kp np j = qOf s.mem kp np j := by
        simp only [qOf]
        rw [wordOf_frame f₁ (hk.sub_left hsub) (hn.sub_left hsub) (by lit_omega),
          wordOf_frame f₁ (hk.sub_left hsub) (hn.sub_left hsub) (by lit_omega)]
      rw [m₂, hq]
      by_cases h : i = 2 * j ∨ i = 2 * j + 1
      · rcases h with rfl | rfl
        · rw [show off c (o + 4 * (2 * j)) = off c (o + 8 * j) by congr 1; omega]
          exact (readW_qword _ _ _ _).1
        · rw [show off c (o + 4 * (2 * j + 1)) = off c (o + 8 * j) + BitVec.ofNat 64 4 by
            rw [off_eq, off_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
          exact (readW_qword _ _ _ _).2
      · rw [off_eq, off_eq, VG.X86_64.readW_writeW_off _ _ _ (n := 4) (by lit_omega) (by lit_omega) (by
          simp only [Nat.reduceDiv]; omega)]
        rw [← off_eq]
        exact w₁ i (by omega)

/-- The ChaCha20 state, a quadword at a time. -/
theorem initStateQ_ok {c kp np : Addr} {o : Nat} (ho : o + 64 ≤ 1696) {s : State}
    (hr15 : s.gpr .r15 = c) (hrdi : s.gpr .rdi = kp) (hrsi : s.gpr .rsi = np) (hc : CtxOk c kp np s)
    (hk : (⟨off c o, 64⟩ : Region).Disjoint ⟨kp, 32⟩) (hn : (⟨off c o, 64⟩ : Region).Disjoint ⟨np, 12⟩) :
    WP isa (.block (initStateQ o)) s fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨off c o, 64⟩] s.mem s'.mem ∧
      ∀ i < 16, s'.mem.readW (off c (o + 4 * i)) 32 = wordOf s.mem kp np i :=
  initStateQ_ok' (j := 8) ho (Nat.le_refl _) hr15 hrdi hrsi hc hk hn

theorem consts_eq : ∀ i < 4, ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] : List (BitVec 32)).getD i 0 =
    Spec.ChaCha20.constants.getD i 0 := by decide

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce. -/
theorem stateAt_initState {s₀ : State} (hp : APre e s₀) {m₁ m' : Mem} {o : Nat}
    (hf₁ : Frame [sub s₀ 0 48] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (o + 4 * i)) 32 = wordOf m₁ (kp s₀) (np s₀) i) :
    stateAt m' (off (cx s₀) o) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  have r₁ : ∀ {p : Addr} {n : Nat}, (ctxR s₀).Disjoint ⟨p, n⟩ → ∀ a, a + 4 ≤ n →
      m₁.readW (off p a) 32 = s₀.mem.readW (off p a) 32 := by
    intro p n hd a ha
    refine hf₁.readW (r := ⟨off p a, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [off_eq]
    exact ((hd.sub_left (sub_ctx s₀ (k := 0) (n := 48) (by lit_omega))).sub_right
      (Offset.sub_base p (d := a) (n := 4) ha)).symm
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [show off (cx s₀) o + BitVec.ofNat 64 (4 * i) = off (cx s₀) (o + 4 * i) by
    simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc], hw i hi]
  unfold wordOf
  split_ifs with h₁ h₂ h₃
  · exact consts_eq i h₁
  · rw [r₁ hp.c_k _ (by lit_omega), show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (kp s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (kp s₀) (n := 32) (j := i - 4) (by lit_omega), off_eq]
  · rfl
  · rw [r₁ hp.c_n _ (by lit_omega), show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (np s₀) 12 from rfl,
      wordLE_bytesAt s₀.mem (np s₀) (n := 12) (j := i - 13) (by lit_omega), off_eq]

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by lit_omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## The keystream from counter 0 -/

/-- The number of bytes of data whose keystream the prologue computes with
the one-time key: all of them if there are at most `fold`, else none. -/
def mOf (fold len : Nat) : Nat := if len ≤ fold then len else 0

theorem mOf_le (fold len : Nat) : mOf fold len ≤ fold := by unfold mOf; split <;> omega
theorem mOf_le_len (fold len : Nat) : mOf fold len ≤ len := by unfold mOf; split <;> omega

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem initState_ctr (key nonce : List Byte) (j : Nat) :
    VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState key 0 nonce) (1 + j) =
      VG.Proof.ChaCha20.ctr (Spec.ChaCha20.initState key 1 nonce) j := by
  apply Vector.ext
  intro i hi
  simp only [VG.Proof.ChaCha20.ctr, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true, Spec.ChaCha20.initState, Vector.getElem_ofFn, show ¬ (12 < 4) by decide,
      show ¬ (12 < 12) by decide, ite_false, BitVec.ofNat_add]
    exact BitVec.zero_add _
  · simp only [h, ite_false, Spec.ChaCha20.initState, Vector.getElem_ofFn, show ¬ i = 12 from fun h' => h h'.symm]

/-- Byte `64 + k` of the keystream from counter 0 is byte `k` of that from
counter 1. -/
theorem keystream_shift (key nonce : List Byte) {n L k : Nat} (hk : k < L) (hn : 64 + k < n) :
    (keystream (Spec.ChaCha20.initState key 0 nonce) n).getD (64 + k) 0 =
      (keystream (Spec.ChaCha20.initState key 1 nonce) L).getD k 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ hn, VG.Proof.ChaCha20.keystream_getD _ hk,
    show (64 + k) / 64 = 1 + k / 64 by omega, show (64 + k) % 64 = k % 64 by omega, initState_ctr]

/-- The first 32 bytes of the keystream from counter 0 are the one-time key. -/
theorem keystream_otk (key nonce : List Byte) {n : Nat} (hn : 32 ≤ n) :
    (keystream (Spec.ChaCha20.initState key 0 nonce) n).take 32 =
      Spec.ChaCha20Poly1305.polyKeyGen key nonce := by
  apply List.ext_getElem
  · simp [VG.Proof.ChaCha20.length_keystream, Spec.ChaCha20Poly1305.polyKeyGen,
      Spec.ChaCha20.chacha20Block, VG.Proof.ChaCha20.length_serialize]; omega
  · intro i h₁ h₂
    simp only [List.length_take, VG.Proof.ChaCha20.length_keystream] at h₁
    have e := VG.Proof.ChaCha20.keystream_getD (Spec.ChaCha20.initState key 0 nonce) (n := n) (k := i)
      (by omega)
    rw [show i / 64 = 0 by omega, show i % 64 = i by omega, VG.Proof.ChaCha20.ctr_zero] at e
    simp only [List.getElem_take, Spec.ChaCha20Poly1305.polyKeyGen, Spec.ChaCha20.chacha20Block]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_keystream]; omega), Option.getD_some] at e
    rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega), Option.getD_some]

/-! ## `m` and the zeros -/

theorem foldM_ok {fold len : Nat} (hf : fold + 1 < 2 ^ 31) (hl : len < 2 ^ 64) {s : State}
    (hr13 : s.gpr .r13 = BitVec.ofNat 64 len) :
    WP isa (foldM fold) s fun s' => s'.gpr .rdx = BitVec.ofNat 64 (mOf fold len) ∧
      (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  unfold foldM
  refine WP.seq (WP.mono (Q := fun (s' : State) => s'.gpr .rdx = 0 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.cf = some (decide (len < fold + 1))) ?_
    fun s₁ ⟨d₁, g₁, rd₁, wr₁, m₁, c₁⟩ => ?_)
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags,
      State.setReg32, State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', se_ofNat hf, reduceCtorEq, ↓reduceIte]
    refine ⟨rfl, fun q hq => by simp [hq], trivial, trivial, trivial, ?_⟩
    rw [hr13, toNat_ofNat_lt hl, toNat_ofNat_lt (by lit_omega)]
  · refine WP.ite (decide (len < fold + 1)) (by simp [eval, c₁]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
        Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
      refine ⟨by rw [g₁ _ (by decide), hr13]; simp only [mOf, show len ≤ fold from by omega, ite_true],
        fun q hq => by simp [hq, g₁ q hq], rd₁, wr₁, m₁⟩
    · simp only [decide_eq_false_iff_not] at h
      exact WP.block_nil (M := isa) ⟨by rw [d₁]; simp only [mOf, show ¬ len ≤ fold from by omega, ite_false]; rfl,
        g₁, rd₁, wr₁, m₁⟩

theorem se64' : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide

theorem add64_ok {n : Nat} {s : State} (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .add .rdx (.imm 64)]) s fun s' => s'.gpr .rdx = BitVec.ofNat 64 (64 + n) ∧
      (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setReg,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se64', ite_true]
  refine ⟨by rw [hrdx, BitVec.ofNat_add, BitVec.add_comm]; rfl, fun q hq => by simp [hq], trivial, trivial,
    trivial⟩

theorem se16' : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide

/-- A 16-byte store of zeros. -/
theorem writeW128_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 128)) x = if (x - a).toNat < 16 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- Before 16-byte word `i` of `ctx[672, 1696)` is zeroed, from the state `s₂`. -/
structure ZInv (s₀ s₂ : State) (i : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = BitVec.ofNat 64 (16 * i)
  x0 : s.xmm .xmm0 = 0
  keep : ∀ r, r ≠ .rcx → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 672 (16 * i)] s₂.mem s.mem
  zero : ∀ k < 16 * i, s.mem (off (cx s₀) (672 + k)) = 0

def zeroBody : List Instr := [.movdquStore zeroQ .xmm0, .alu .add .rcx (.imm 16), .alu .cmp .rcx (.reg .rdx)]

theorem zero_step {s₀ : State} (hp : APre e s₀) {s₂ : State} {n : Nat} (hn : n ≤ 1024)
    (hrdx : s₂.gpr .rdx = BitVec.ofNat 64 n) (hr15 : s₂.gpr .r15 = cx s₀) (hwr : s₂.wr = s₀.wr)
    {i : Nat} (hi : 16 * i < n) {s : State} (h : ZInv s₀ s₂ i s) :
    WP isa (.block zeroBody) s fun s' =>
      ZInv s₀ s₂ (i + 1) s' ∧ s'.cf = some (decide (16 * (i + 1) < n)) := by
  have hrdx' : s.gpr .rdx = BitVec.ofNat 64 n := by rw [h.keep _ (by decide), hrdx]
  have hr15' : s.gpr .r15 = cx s₀ := by rw [h.keep _ (by decide), hr15]
  have ea : cx s₀ + BitVec.ofNat 64 (16 * i) * BitVec.ofNat 64 1 + BitVec.ofInt 64 672 = off (cx s₀) (672 + 16 * i) := by
    rw [BitVec.mul_one, off_eq, show BitVec.ofInt 64 672 = BitVec.ofNat 64 672 by decide, BitVec.ofNat_add,
      BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (16 * i))]
  have hout : InRegions s.wr (off (cx s₀) (672 + 16 * i)) 16 := by rw [h.wr, hwr]; exact hp.in_ctx (by lit_omega)
  have e16 : BitVec.ofNat 64 (16 * i) + 16 = BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [show 16 * (i + 1) = 16 * i + 16 by omega, BitVec.ofNat_add]; rfl
  apply WP.of_runBlock
  simp only [zeroBody, zeroQ, runBlock_cons, runStep_some, runBlock_nil, exec, State.ea, readSrc, execAlu,
    arithFlags, State.store128, State.setReg, State.setFlags, hr15', h.rcx, h.x0, ea, hout,
    Option.bind_some, Option.some.injEq, exists_eq_left', se16', reduceCtorEq, ↓reduceIte, e16, hrdx']
  refine ⟨⟨rfl, h.x0, fun r h₁ => by simp [h₁, h.keep r h₁], h.rd, h.wr, ?_, fun k hk => ?_⟩, ?_⟩
  · exact (h.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨sub s₀ 672 (16 * (i + 1)), List.mem_singleton_self _,
          sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · dsimp only
    rw [writeW128_zero_apply]
    by_cases hk' : k < 16 * i
    · split
      · rfl
      · exact h.zero k hk'
    · rw [off_eq, off_eq, Offset.sub_toNat _ (by lit_omega) (by lit_omega)]
      simp only [show 672 + k - (672 + 16 * i) < 16 by omega, ite_true]
  · rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)]

/-- Zeroing the first `n` bytes of `ctx[672, 1696)` (and up to 15 more). -/
theorem zeroKs_ok {s₀ : State} (hp : APre e s₀) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 1024) {s : State}
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hr15 : s.gpr .r15 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa zeroKs s fun s' =>
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 672 1024] s.mem s'.mem ∧ ∀ k < n, s'.mem (off (cx s₀) (672 + k)) = 0 := by
  unfold zeroKs
  refine WP.seq (WP.mono (Q := fun (s' : State) => s'.xmm .xmm0 = 0 ∧ s'.gpr .rcx = 0 ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem) ?_
    fun s₂ ⟨x₂, c₂, g₂, rd₂, wr₂, m₂⟩ => ?_)
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32, State.setReg,
      XOp.exec, XBinOp.eval, State.setXmm, Option.map_some, Option.some.injEq, exists_eq_left',
      ↓reduceIte, BitVec.xor_self]
    exact ⟨rfl, rfl, fun r h₁ => by simp [h₁], trivial, trivial, trivial⟩
  have hr15₂ : s₂.gpr .r15 = cx s₀ := by rw [g₂ _ (by decide), hr15]
  have hrdx₂ : s₂.gpr .rdx = BitVec.ofNat 64 n := by rw [g₂ _ (by decide), hrdx]
  let Inv : Nat → State → Prop := fun k s => ∃ i, k = n - 16 * i ∧ 16 * i < n ∧ ZInv s₀ s₂ i s
  have hstep : ∀ k s, Inv k s → WP isa (.block zeroBody) s (fun s' =>
      (eval .b s' = some false ∧ ∃ i, n ≤ 16 * i ∧ 16 * i < n + 16 ∧ ZInv s₀ s₂ i s') ∨
      (eval .b s' = some true ∧ ∃ k' < k, Inv k' s')) := by
    rintro k s ⟨i, rfl, hi, hI⟩
    refine WP.mono (zero_step hp hn hrdx₂ hr15₂ (by rw [wr₂, hwr]) hi hI) fun s' ⟨h', hc⟩ => ?_
    by_cases hl : 16 * (i + 1) < n
    · exact .inr ⟨by simp [eval, hc, hl], n - 16 * (i + 1), by omega, i + 1, rfl, hl, h'⟩
    · exact .inl ⟨by simp [eval, hc, hl], i + 1, by omega, by omega, h'⟩
  refine WP.mono (WP.loop (M := isa) Inv hstep (n - 16 * 0) s₂ ⟨0, rfl, by omega,
    ⟨by rw [c₂]; rfl, x₂, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun k hk => absurd hk (by omega)⟩⟩)
    fun s' ⟨i, hi₁, hi₂, hI⟩ => ?_
  refine ⟨fun r h₁ h₂ => by rw [hI.keep r h₂, g₂ r h₂], by rw [hI.rd, rd₂], by rw [hI.wr, wr₂], ?_,
    fun k hk => hI.zero k (by omega)⟩
  rw [← m₂]
  exact hI.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩

/-! ## The whole prologue -/

/-- The entry. -/
theorem entry_ok {s₀ : State} (hp : APre e s₀) : WP isa (.block entry) s₀ fun s => s = entryS s₀ :=
  ⟨_, _, Exec.block (entry_run hp), rfl⟩

/-- At the call of `vg_chacha20_xor` in the prologue, for `m = mOf fold len`. -/
structure FArgs (fold : Nat) (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 608
  rsi : s.gpr .rsi = off (cx s₀) 672
  rdx : s.gpr .rdx = BitVec.ofNat 64 (64 + mOf fold (L s₀))
  rcx : s.gpr .rcx = off (cx s₀) 128
  r15 : s.gpr .r15 = cx s₀
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = ad s₀
  rbp : s.gpr .rbp = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  st' : stateAt s.mem (off (cx s₀) 608) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  zero : ∀ k < 64 + mOf fold (L s₀), s.mem (off (cx s₀) (672 + k)) = 0

theorem B1_eq : save ++ moves ++ initStateQ 64 ++ initStateQ 608 =
    (save ++ moves) ++ (initStateQ 64 ++ initStateQ 608) := by
  simp only [List.append_assoc]

theorem FA_eq : ptr .rdi .r15 608 ++ ptr .rsi .r15 672 ++ ptr .rcx .r15 128 =
    ptr .rdi .r15 608 ++ (ptr .rsi .r15 672 ++ ptr .rcx .r15 128) := by
  simp only [List.append_assoc]

theorem prologueA_ok {fold : Nat} (hf : fold ≤ 960) {s₀ : State} (hp : APre e s₀) :
    WP isa (prologueA fold) (entryS s₀) (FArgs fold s₀) := by
  have hL9 := (s₀.gpr .r9).isLt
  have hm := mOf_le fold (L s₀)
  unfold prologueA
  rw [B1_eq]
  -- The registers, the saved ones and the two ChaCha20 states.
  refine WP.seq (WP.block_append (WP.mono (saveMoves_ok hp)
    fun s₁ ⟨e15, e12, ebx, ebp, e14, e13, g₁, rd₁, wr₁, f₁, sv₁⟩ => ?_))
  have edi : s₁.gpr .rdi = kp s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have esi : s₁.gpr .rsi = np s₀ := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ersp : s₁.gpr .rsp = s₀.gpr .rsp := g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hc₁ : CtxOk (cx s₀) (kp s₀) (np s₀) s₁ := by
    refine ⟨fun a w h => by rw [rd₁, wr₁]; exact ⟨hp.in_ctx' h, hp.in_ctx h⟩, fun a w ha => ?_, fun a w ha => ?_⟩
    · rw [rd₁, wr₁]
      exact ⟨kR s₀, by simp [hp.k_rd], by rw [off_eq]; exact Offset.contains_base _ ha (by lit_omega)⟩
    · rw [rd₁, wr₁]
      exact ⟨nR s₀, by simp [hp.n_rd], by rw [off_eq]; exact Offset.contains_base _ ha (by lit_omega)⟩
  refine WP.block_append (WP.mono (initStateQ_ok (o := 64) (by lit_omega) e15 edi esi hc₁
    (hp.c_k.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
    (hp.c_n.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))))
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, w₂⟩ => ?_)
  have hc₂ : CtxOk (cx s₀) (kp s₀) (np s₀) s₂ := by rw [CtxOk, rd₂, wr₂]; exact hc₁
  refine WP.mono (initStateQ_ok (o := 608) (by lit_omega)
    (by rw [g₂ _ (by decide), e15]) (by rw [g₂ _ (by decide), edi]) (by rw [g₂ _ (by decide), esi]) hc₂
    (hp.c_k.sub_left (sub_ctx s₀ (k := 608) (n := 64) (by lit_omega)))
    (hp.c_n.sub_left (sub_ctx s₀ (k := 608) (n := 64) (by lit_omega))))
    fun s₃ ⟨g₃, rd₃, wr₃, f₃, w₃⟩ => ?_
  have g₃' : ∀ r, r ≠ .rax → s₃.gpr r = s₁.gpr r := fun r h => by rw [g₃ r h, g₂ r h]
  have d64 : (⟨off (cx s₀) 64, 64⟩ : Region).Disjoint ⟨off (cx s₀) 608, 64⟩ :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hw₃ : ∀ i < 16, s₃.mem.readW (off (cx s₀) (608 + 4 * i)) 32 = wordOf s₁.mem (kp s₀) (np s₀) i := by
    intro i hi
    rw [w₃ i hi, wordOf_frame f₂ (hp.c_k.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
      (hp.c_n.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))) hi]
  -- `m`, `64 + m` and the zeros.
  refine WP.seq (WP.mono (foldM_ok (fold := fold) (len := L s₀) (by lit_omega) hL9
    (by rw [g₃' _ (by decide), e13]; simp [L])) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (add64_ok (n := mOf fold (L s₀)) d₄) fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ => ?_)
  have r15₅ : s₅.gpr .r15 = cx s₀ := by rw [g₅ _ (by decide), g₄ _ (by decide), g₃' _ (by decide), e15]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, wr₃, wr₂, wr₁]
  refine WP.seq (WP.mono (zeroKs_ok hp (n := 64 + mOf fold (L s₀)) (by omega) (by lit_omega) d₅ r15₅ wr₅')
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, z₆⟩ => ?_)
  -- The arguments.
  rw [FA_eq]
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 608) (by lit_omega) s₆)
    fun s₇ ⟨e7, g₇, rd₇, wr₇, m₇⟩ => ?_)
  refine WP.block_append (WP.mono (ptr_ok .rsi .r15 (k := 672) (by lit_omega) s₇)
    fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ => ?_)
  refine WP.mono (ptr_ok .rcx .r15 (k := 128) (by lit_omega) s₈) fun s₉ ⟨e9, g₉, rd₉, wr₉, m₉⟩ => ?_
  have gg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rdi → r ≠ .rsi → s₉.gpr r = s₁.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [g₉ r h₂, g₈ r h₅, g₇ r h₄, g₆ r h₁ h₂, g₅ r h₃, g₄ r h₃, g₃' r h₁]
  have r15₉ : s₉.gpr .r15 = cx s₀ := by
    rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), e15]
  have mm : s₉.mem = s₆.mem := by rw [m₉, m₈, m₇]
  have m₅' : s₅.mem = s₃.mem := by rw [m₅, m₄]
  -- The memory.
  have sub1 : ∀ {k n : Nat}, 0 ≤ k → k + n ≤ 1696 → Region.Sub (sub s₀ k n) (workR s₀) :=
    fun h₁ h₂ => sub_sub s₀ h₁ (by lit_omega) (by lit_omega)
  have fwork : ∀ {k n : Nat} {m m' : Mem}, k + n ≤ 1696 → Frame [sub s₀ k n] m m' → Frame [workR s₀, stkR s₀] m m' :=
    fun h hf => hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨workR s₀, by simp, sub1 (Nat.zero_le _) h⟩
  have ff : Frame [workR s₀, stkR s₀] s₀.mem s₉.mem := by
    rw [mm]
    refine (fwork (k := 0) (n := 48) (by lit_omega) f₁).trans ((fwork (k := 64) (n := 64) (by lit_omega) f₂).trans
      ((fwork (k := 608) (n := 64) (by lit_omega) f₃).trans ?_))
    rw [← m₅']; exact fwork (k := 672) (n := 1024) (by lit_omega) f₆
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    refine stateAt_initState hp f₁ fun i hi => ?_
    rw [f₃.readW (r := ⟨off (cx s₀) (64 + 4 * i), 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton, forall_eq]
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by decide), w₂ i hi]
  have st₃' : stateAt s₃.mem (off (cx s₀) 608) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) :=
    stateAt_initState hp f₁ hw₃
  have dz : ∀ {k : Nat}, k + 64 ≤ 672 → ∀ r ∈ [sub s₀ 672 1024], (⟨off (cx s₀) k, 64⟩ : Region).Disjoint r := by
    intro k hk r hr; simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  refine ⟨by rw [g₉ _ (by decide), g₈ _ (by decide), e7, g₆ _ (by decide) (by decide), r15₅],
    by rw [g₉ _ (by decide), e8, g₇ _ (by decide), g₆ _ (by decide) (by decide), r15₅],
    by rw [g₉ _ (by decide), g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide) (by decide), d₅],
    by rw [e9, g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide) (by decide), r15₅], r15₉,
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), e14],
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), e13],
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), e12],
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), ebx],
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), ebp],
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide), ersp],
    by rw [rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₉, wr₈, wr₇, wr₆, wr₅'],
    ?_, ff, ?_, ?_, fun k hk => by rw [mm]; exact z₆ k hk⟩
  · rw [mm]
    refine ((sv₁.frame f₂ ?_).frame f₃ ?_).frame (by rw [← m₅']; exact f₆) ?_
    · simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  · rw [mm, stateAt_frame f₆ (dz (by lit_omega)), m₅', st₃]
  · rw [mm, stateAt_frame f₆ (dz (by lit_omega)), m₅', st₃']

/-- After the call of `vg_chacha20_xor` in the prologue. -/
structure AfterF (fold : Nat) (s₀ : State) (s : State) : Prop where
  rsi : s.gpr .rsi = off (cx s₀) 128
  r14 : s.gpr .r14 = dp s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r12 : s.gpr .r12 = tp s₀
  rbx : s.gpr .rbx = ad s₀
  rbp : s.gpr .rbp = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  ks : ∀ k < 64 + mOf fold (L s₀), s.mem (off (cx s₀) (672 + k)) =
    (keystream (Spec.ChaCha20.initState (K s₀) 0 (N s₀)) (64 + mOf fold (L s₀))).getD k 0

/-- The call of the implementation `v` of `vg_chacha20_xor` in the prologue. -/
theorem foldCall_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : FArgs v.callee.fold s₀ s) :
    WP isa (.call v.callee.name v.callee.code) s (AfterF v.callee.fold s₀) := by
  have hm := mOf_le v.callee.fold (L s₀)
  have hfl := v.fold_le
  have hn : 64 + mOf v.callee.fold (L s₀) ≤ 1024 := by omega
  refine xor_call v h.rdi h.rsi h.rdx h.rcx (by lit_omega)
    (sub_disj s₀ (b := 672) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 672) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))
    (Covers.right (covers_sub hp h.wr _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨608, rfl, show 608 + 64 ≤ 1696 by omega⟩
      · exact ⟨672, rfl, show 672 + (64 + mOf v.callee.fold (L s₀)) ≤ 1696 by omega⟩
      · exact ⟨128, rfl, show 128 + 320 ≤ 1696 by omega⟩)))
    (covers_sub hp h.wr _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨608, rfl, show 608 + 64 ≤ 1696 by omega⟩
      · exact ⟨672, rfl, show 672 + (64 + mOf v.callee.fold (L s₀)) ≤ 1696 by omega⟩
      · exact ⟨128, rfl, show 128 + 320 ≤ 1696 by omega⟩))
    fun s' rd' wr' cs' f' rsi' ks' => ?_
  rw [h.rsp] at f'
  have fw : Frame [workR s₀, stkR s₀] s.mem s'.mem := f'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have dsv : ∀ r ∈ [(⟨off (cx s₀) 608, 64⟩ : Region), ⟨off (cx s₀) 672, 64 + mOf v.callee.fold (L s₀)⟩,
      ⟨off (cx s₀) 128, 320⟩, stkR s₀], (sub s₀ 0 48).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (b := 672) (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.stk_sub (by lit_omega)).symm
  have dst : ∀ r ∈ [(⟨off (cx s₀) 608, 64⟩ : Region), ⟨off (cx s₀) 672, 64 + mOf v.callee.fold (L s₀)⟩,
      ⟨off (cx s₀) 128, 320⟩, stkR s₀], (⟨off (cx s₀) 64, 64⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (b := 672) (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.stk_sub (by lit_omega)).symm
  refine ⟨rsi', by rw [cs' _ (by simp [calleeSaved]), h.r14], by rw [cs' _ (by simp [calleeSaved]), h.r13],
    by rw [cs' _ (by simp [calleeSaved]), h.r12], by rw [cs' _ (by simp [calleeSaved]), h.rbx],
    by rw [cs' _ (by simp [calleeSaved]), h.rbp], by rw [cs' _ (by simp [calleeSaved]), h.rsp],
    by rw [rd', h.rd], by rw [wr', h.wr], h.saved.frame f' dsv, h.fine.trans fw,
    by rw [stateAt_frame f' dst, h.st], fun k hk => ?_⟩
  rw [h.st'] at ks'
  have := VG.Proof.ChaCha20.X86_64.Avx2.bytes_of_bytesAt (VG.Proof.ChaCha20.length_keystream _ _) ks' hk
  rw [show off (cx s₀) 672 + BitVec.ofNat 64 k = off (cx s₀) (672 + k) by
    rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc]] at this
  rw [this, h.zero k hk]; simp

/-- After the prologue. -/
structure PostP (fold : Nat) (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  rbx : s.gpr .rbx = ad s₀
  rbp : s.gpr .rbp = s₀.gpr .rcx
  fine : Frame [workR s₀, stkR s₀] s₀.mem s.mem
  poly : Repr s.mem (off (cx s₀) 448) (otk s₀) []
  st : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  ks : ∀ k < mOf fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
    (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0

theorem B3_eq : anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 672 =
    anchor .rsi 128 ++ (ptr .rdi .r15 448 ++ ptr .rsi .r15 672) := by
  simp only [List.append_assoc]

theorem prologueB_ok {fold : Nat} (hf : fold ≤ 960) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : AfterF fold s₀ s) : WP isa prologueB s (PostP fold s₀) := by
  have hm := mOf_le fold (L s₀)
  have hml := mOf_le_len fold (L s₀)
  unfold prologueB
  rw [B3_eq]
  refine WP.seq (WP.block_append (WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s)
    fun s₆ ⟨e6, g₆, rd₆, wr₆, m₆⟩ => ?_))
  have r15₆ : s₆.gpr .r15 = cx s₀ := by rw [e6, h.rsi, off_sub]
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by lit_omega) s₆)
    fun s₇ ⟨e7, g₇, rd₇, wr₇, m₇⟩ => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 672) (by lit_omega) s₇) fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ => ?_
  have rdi₈ : s₈.gpr .rdi = off (cx s₀) 448 := by rw [g₈ _ (by decide), e7, r15₆]
  have rsi₈ : s₈.gpr .rsi = off (cx s₀) 672 := by rw [e8, g₇ _ (by decide), r15₆]
  have g₈' : ∀ r, r ≠ .r15 → r ≠ .rdi → r ≠ .rsi → s₈.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g₈ r h₃, g₇ r h₂, g₆ r h₁]
  have rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by rw [g₈' _ (by decide) (by decide) (by decide), h.rsp]
  have wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇, wr₆, h.wr]
  have mm₈ : s₈.mem = s.mem := by rw [m₈, m₇, m₆]
  -- The Poly1305 state for the one-time key.
  refine WP.seq (init_call rdi₈ rsi₈ (sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [rsp₈]; exact hp.below8_sub (by lit_omega)) (by rw [rsp₈]; exact hp.below8_sub (by lit_omega))
    (Covers.right (covers_sub hp wr₈' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨672, rfl, show 672 + 32 ≤ 1696 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩)))
    (covers_sub hp wr₈' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩))
    fun s₉ rd₉ wr₉ cs₉ f₉ rdi₉ repr₉ => ?_)
  rw [rsp₈] at f₉
  refine WP.mono (anchor_ok .rdi (k := 448) (by lit_omega) s₉) fun s₁₀ ⟨e10, g₁₀, rd₁₀, wr₁₀, m₁₀⟩ => ?_
  have cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s₁₀.gpr r = s.gpr r := fun r hr h15 => by
    have h' : r ≠ .rdi ∧ r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₁₀ r h15, cs₉ r hr, g₈' r h15 h'.1 h'.2]
  have d9 : ∀ {k n : Nat}, k + n ≤ 448 ∨ 576 ≤ k → k + n ≤ 1696 → ∀ r ∈ [sub s₀ 448 128, below (s₀.gpr .rsp) 8],
      (sub s₀ k n).Disjoint r := by
    intro k n h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact (hp.below8_sub (by lit_omega)).symm
  have ff : Frame [workR s₀, stkR s₀] s.mem s₁₀.mem := by
    rw [m₁₀, ← mm₈]
    exact f₉.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, below8_stk s₀⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, h.rd], by rw [wr₁₀, wr₉, wr₈'], ?_,
    (h.fine.trans ff).sub fun r hr => ?_⟩, ?_, ?_, h.fine.trans ff, ?_, ?_, fun k hk => ?_⟩
  · rw [e10, rdi₉, off_sub]
  · rw [cs .r14 (by simp [calleeSaved]) (by decide), h.r14]
  · rw [cs .r13 (by simp [calleeSaved]) (by decide), h.r13]
  · rw [cs .r12 (by simp [calleeSaved]) (by decide), h.r12]
  · rw [g₁₀ _ (by decide), cs₉ _ (by simp [calleeSaved]), rsp₈]
  · rw [m₁₀]
    exact h.saved.frame (by rw [← mm₈]; exact f₉) (d9 (by lit_omega) (by lit_omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨workR s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · rw [cs .rbx (by simp [calleeSaved]) (by decide), h.rbx]
  · rw [cs .rbp (by simp [calleeSaved]) (by decide), h.rbp]
  · rw [m₁₀]
    have hk : bytesAt s₈.mem (off (cx s₀) 672) 32 = otk s₀ := by
      show _ = Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)
      rw [mm₈, ← keystream_otk (K s₀) (N s₀) (n := 64 + mOf fold (L s₀)) (by omega)]
      apply List.ext_getElem
      · simp [bytesAt, VG.Proof.ChaCha20.length_keystream]; omega
      · intro i h₁ h₂
        simp only [bytesAt, List.length_map, List.length_range] at h₁
        simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take]
        rw [show off (cx s₀) 672 + BitVec.ofNat 64 i = off (cx s₀) (672 + i) by
          rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], h.ks i (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
            rw [VG.Proof.ChaCha20.length_keystream]; omega), Option.getD_some]
        rfl
    rw [← hk]; exact repr₉
  · rw [m₁₀, stateAt_frame f₉ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact (hp.below8_sub (by lit_omega)).symm), mm₈, h.st]
  · have e : s₁₀.mem (off (cx s₀) (736 + k)) = s.mem (off (cx s₀) (736 + k)) := by
      rw [m₁₀, ← mm₈]
      exact f₉ _ fun r hr hc => d9 (k := 736 + k) (n := 1) (by lit_omega) (by lit_omega) r hr _
        (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
    rw [e, show 736 + k = 672 + (64 + k) by omega, h.ks (64 + k) (by omega),
      keystream_shift (K s₀) (N s₀) (L := L s₀) (n := 64 + mOf fold (L s₀)) (by omega) (by omega)]

theorem prologue_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) :
    WP isa (prologue v.callee) (entryS s₀) (PostP v.callee.fold s₀) :=
  WP.seq (WP.mono (prologueA_ok v.fold_le hp) fun _ h =>
    WP.seq (WP.mono (foldCall_ok v hp h) fun _ h' => prologueB_ok v.fold_le hp h'))

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: absorbing padded data

`macPad p n` absorbs the `n` bytes at `p` into the Poly1305 state, and zeros
to a multiple of 16: `msg ++ x ++ pad16 x`.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-- The registers `macPad` may take its arguments in. -/
def MacRegs (p n : Reg) : Prop := (p = .rbx ∨ p = .r14) ∧ (n = .rbp ∨ n = .r13)

/-- What `macPad` needs of the bytes it absorbs. -/
structure Src (s₀ : State) (P : Addr) (len : Nat) : Prop where
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  ctx : (ctxR s₀).Disjoint ⟨P, len⟩
  stk : (stkR s₀).Disjoint ⟨P, len⟩
  cov : Covers [⟨P, len⟩] (s₀.rd ++ s₀.wr)

theorem contains_off_sub {P : Addr} {a n len w : Nat} {x : Addr} (h : a + n ≤ len)
    (hc : (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Contains x w) : (⟨P, len⟩ : Region).Contains x w := by
  simp only [Region.Contains] at *
  have : (x - P).toNat ≤ (x - (P + BitVec.ofNat 64 a)).toNat + a := by
    rw [show x - P = (x - (P + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by
      rw [Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem Src.cov_sub {s₀ : State} {P : Addr} {len : Nat} (hs : Src s₀ P len) {a n : Nat} (h : a + n ≤ len)
    {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers [⟨P + BitVec.ofNat 64 a, n⟩] (s.rd ++ s.wr) := by
  intro x w ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [hrd, hwr]
  exact hs.cov x w ⟨_, List.mem_singleton_self _, contains_off_sub h hc⟩

theorem Src.disj_sub {P : Addr} {len : Nat} {R : Region} (hd : R.Disjoint ⟨P, len⟩) {a n : Nat}
    (h : a + n ≤ len) : R.Disjoint ⟨P + BitVec.ofNat 64 a, n⟩ :=
  fun x h₁ h₂ => hd x h₁ (contains_off_sub h h₂)

set_option simprocs false in
theorem macA_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ([.mov .rsi (.reg p), .mov .rdx (.reg n), .shift .shr .rdx 4] : List Instr))) s
      fun s' => s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = s.gpr p ∧
        s'.gpr .rdx = s.gpr n >>> 4 ∧ s'.zf = some (s.gpr n >>> 4 == 0) ∧
        (∀ q, q ≠ .rdi → q ≠ .rsi → q ≠ .rdx → s'.gpr q = s.gpr q) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  refine WP.block_append (WP.mono (ptr_ok .rdi .r15 (k := 448) (by lit_omega) s)
    fun s₁ ⟨e1, g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hp₁ : s₁.gpr p = s.gpr p := g₁ p (by rcases hp with rfl | rfl <;> decide)
  have hn₁ : s₁.gpr n = s.gpr n := g₁ n (by rcases hn with rfl | rfl <;> decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, State.setReg, State.setFlags, Option.map_some, Option.some.injEq, exists_eq_left',
    ite_true, ite_false]
  have hpd : p ≠ .rdx := by rcases hp with rfl | rfl <;> decide
  have hnd : n ≠ .rsi := by rcases hn with rfl | rfl <;> decide
  refine ⟨by simp [e1], by simp [hp₁], by simp [hnd, hn₁], by simp [hnd, hn₁],
    fun q h₁ h₂ h₃ => by simp [h₂, h₃, g₁ q h₁], rd₁, wr₁, m₁⟩

set_option simprocs false in
theorem macC_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.mov .rdx (.reg n), .alu .and .rdx (.imm 15)]) s
      fun s' => s'.gpr .rdx = s.gpr n &&& 15 ∧ s'.zf = some (s.gpr n &&& 15 == 0) ∧
        (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  have se15 : BitVec.signExtend 64 (15 : BitVec 32) = 15 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, se15]
  refine ⟨by simp, by simp, fun q h₁ => by simp [h₁], trivial⟩

set_option simprocs false in
theorem macD_ok {p n : Reg} (hr : MacRegs p n) (s : State) :
    WP isa (.block [.mov .rsi (.reg n), .alu .sub .rsi (.reg .rdx), .alu .add .rsi (.reg p)]) s
      fun s' => s'.gpr .rsi = s.gpr n - s.gpr .rdx + s.gpr p ∧
        (∀ q, q ≠ .rsi → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  obtain ⟨hp, hn⟩ := hr
  have hps : p ≠ .rsi := by rcases hp with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, hps]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem se0' : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

set_option simprocs false in
/-- Zeroing the padded block. -/
theorem padZ_ok {s₀ : State} (hp : APre e s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
      .mov32 .rcx (.imm 0)]) s fun s' =>
      s'.gpr .rcx = 0 ∧ (∀ q, q ≠ .rax → q ≠ .rcx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [sub s₀ 576 16] s.mem s'.mem ∧ ∀ j < 16, s'.mem (off (cx s₀) (576 + j)) = 0 := by
  have o0 := hp.in_ctx (a := 576) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 584) (w := 8) (by lit_omega)
  rw [← hwr] at o0 o1
  simp only [off] at o0 o1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc32, State.store64, State.setReg, State.setReg32, hr15, o0, o1, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q h₁ h₂ => by simp [h₁, h₂], trivial, trivial, ?_, fun j hj => ?_⟩
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · have z : (BitVec.setWidth 64 (0 : BitVec 32)) = 0 := rfl
    simp only [z]
    rw [VG.Proof.Poly1305.writeW64_zero_apply, VG.Proof.Poly1305.writeW64_zero_apply]
    have e : ∀ d, d ≤ 576 + j → (off (cx s₀) (576 + j) - (cx s₀ + BitVec.ofInt 64 (d : Int))).toNat = 576 + j - d := by
      intro d hd
      rw [show cx s₀ + BitVec.ofInt 64 (d : Int) = off (cx s₀) d from rfl, off_eq, off_eq]
      exact Offset.sub_toNat _ hd (by lit_omega)
    by_cases h : 8 ≤ j
    · rw [e 584 (by lit_omega)]
      simp only [show 576 + j - 584 < 8 by omega, ite_true]
    · have w : ¬ (off (cx s₀) (576 + j) - (cx s₀ + BitVec.ofInt 64 ((584 : Nat) : Int))).toNat < 8 := by
        rw [show cx s₀ + BitVec.ofInt 64 ((584 : Nat) : Int) = off (cx s₀) 584 from rfl, off_eq, off_eq,
          Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
        split <;> omega
      simp only [w, ite_false, e 576 (by lit_omega), show 576 + j - 576 < 8 by omega, ite_true]

/-! ## Copying the last bytes -/

/-- Before byte `i` of the last `t` bytes at `Q` is copied into the padded
block, from the state `s₂` after the block was zeroed. -/
structure CpInv (s₀ s₂ : State) (Q : Addr) (i : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame [sub s₀ 576 16] s₂.mem s.mem
  buf : ∀ j < 16, s.mem (off (cx s₀) (576 + j)) = if j < i then s₂.mem (Q + BitVec.ofNat 64 j) else 0

def copyBody : List Instr :=
  [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1), .alu .cmp .rcx (.reg .rdx)]

theorem se1' : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

set_option simprocs false in
theorem copy_step {s₀ : State} (hp : APre e s₀) {s₂ : State} {Q : Addr} {t : Nat} (ht : t < 16)
    (hrsi : s₂.gpr .rsi = Q) (hrdx : s₂.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s₂.gpr .r15 = cx s₀)
    (hwr : s₂.wr = s₀.wr) (hsrc : ∀ j < t, InRegions (s₂.rd ++ s₂.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < t) {s : State} (h : CpInv s₀ s₂ Q i s) :
    WP isa (.block copyBody) s fun s' =>
      CpInv s₀ s₂ Q (i + 1) s' ∧ s'.zf = some (decide (i + 1 = t)) := by
  have hrsi' : s.gpr .rsi = Q := by rw [h.keep _ (by decide) (by decide), hrsi]
  have hrdx' : s.gpr .rdx = BitVec.ofNat 64 t := by rw [h.keep _ (by decide) (by decide), hrdx]
  have hr15' : s.gpr .r15 = cx s₀ := by rw [h.keep _ (by decide) (by decide), hr15]
  have ea1 : Q + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = Q + BitVec.ofNat 64 i := by simp
  have ea2 : cx s₀ + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 576 = off (cx s₀) (576 + i) := by
    rw [BitVec.mul_one, off_eq, show BitVec.ofInt 64 576 = BitVec.ofNat 64 576 by decide, BitVec.ofNat_add,
      BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i)]
  have hin : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hsrc i hi
  have hout : InRegions s.wr (off (cx s₀) (576 + i)) 1 := by rw [h.wr, hwr]; exact hp.in_ctx (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyBody, tailByte, padByte, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg,
    State.setFlags, hrsi', hr15', h.rcx, ea1, ea2, hin, hout, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1']
  -- The byte copied is byte `i` of the tail, unchanged since `s₂`.
  have hbyte : s.mem (Q + BitVec.ofNat 64 i) = s₂.mem (Q + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hc => hdisj i hi r hr _ (by
      simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine ⟨⟨?_, fun r h₁ h₂ => by simp [h₁, h₂, h.keep r h₁ h₂], h.rd, h.wr, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [ite_true]; rw [BitVec.ofNat_add]; rfl
  · exact h.frame.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  · dsimp only
    rw [VG.Proof.ChaCha20.X86_64.XorBuf.writeW8_apply]
    by_cases hki : k = i
    · subst hki
      simp only [ite_true, show k < k + 1 by omega, BitVec.setWidth_setWidth_of_le _ (by omega :
        8 ≤ 64), BitVec.setWidth_eq, hbyte]
    · have hne : off (cx s₀) (576 + k) ≠ off (cx s₀) (576 + i) := by
        intro he
        rw [off_eq, off_eq] at he
        have := congrArg BitVec.toNat (show BitVec.ofNat 64 (576 + k) = BitVec.ofNat 64 (576 + i) by
          simpa using he)
        rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
        omega
      simp only [hne, ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [hrdx', show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) by rw [BitVec.ofNat_add]; rfl]
    by_cases he : i + 1 = t
    · simp [he]
    · have : BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 t ≠ 0 := by
        intro h0
        have : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 t := by
          rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 t), h0]
          exact BitVec.zero_add _
        have := congrArg BitVec.toNat this
        rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
        exact he this
      simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact this

theorem copyLoop_eq : (Code.loop (.block [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .rdx)]) .ne : Prog isa) = .loop (.block copyBody) .ne := rfl

/-- The padded block's bytes. -/
theorem padded_bytes {s₀ : State} {m mz : Mem} {Q : Addr} {t : Nat} (ht : t < 16)
    (h : ∀ j < 16, m (off (cx s₀) (576 + j)) = if j < t then mz (Q + BitVec.ofNat 64 j) else 0) :
    bytesAt m (off (cx s₀) 576) 16 = bytesAt mz Q t ++ List.replicate (16 - t) 0 := by
  apply List.ext_getElem
  · simp [bytesAt]; omega
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show off (cx s₀) 576 + BitVec.ofNat 64 k = off (cx s₀) (576 + k) by
      rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], h k h₁]
    by_cases hk : k < t
    · rw [List.getElem_append_left (by simp [hk])]
      simp [hk]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [hk]

theorem padE_eq (k : Nat) :
    ptr .rdi .r15 448 ++ ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm (BitVec.ofNat 32 k))] : List Instr) =
    ptr .rdi .r15 448 ++ (ptr .rsi .r15 576 ++ ([.mov32 .rdx (.imm (BitVec.ofNat 32 k))] : List Instr)) := by
  simp only [List.append_assoc]

set_option simprocs false in
theorem mov32_rdx_ok (v : BitVec 32) (s : State) :
    WP isa (.block [.mov32 .rdx (.imm v)]) s fun s' =>
      s'.gpr .rdx = v.setWidth 64 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg32, State.setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun q hq => by simp [hq], trivial⟩

theorem padTail_eq (b : Impl.Poly1305.X86_64.Blocks) (k : Nat) : padTail b k =
    .seq (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
      .mov32 .rcx (.imm 0)])
    (.seq (.loop (.block copyBody) .ne)
    (.seq (.block (ptr .rdi .r15 448 ++ (ptr .rsi .r15 576 ++
      ([.mov32 .rdx (.imm (BitVec.ofNat 32 k))] : List Instr))))
    (.seq (.call b.name b.code) (.block (anchor .rdi 448))))) := by
  rw [padTail, padE_eq]; rfl

/-- The frame of the Poly1305 state and the padded block, and the calls. -/
abbrev macR (s₀ : State) : List Region := [sub s₀ 448 144, stkR s₀]

theorem sub_mac (s₀ : State) {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) : Region.Sub (sub s₀ k n) (sub s₀ 448 144) :=
  sub_sub s₀ h₁ (by lit_omega) (by lit_omega)

theorem frame_mac {s₀ : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) {m m' : Mem}
    (hf : Frame [sub s₀ k n] m m') : Frame (macR s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩

theorem frame_mac' {s₀ : State} {k n : Nat} (h₁ : 448 ≤ k) (h₂ : k + n ≤ 592) {m m' : Mem}
    (hf : Frame [sub s₀ k n, below (s₀.gpr .rsp) 24] m m') : Frame (macR s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, sub_mac s₀ h₁ h₂⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The last `t` bytes at `Q`, padded, absorbed with the `k - 1` blocks after
the padded block (at `ctx + 592`): `k` is 1, or 2 for the lengths block. -/
theorem padTail_ok (b : Impl.Poly1305.X86_64.Blocks) {k : Nat} (hk : k = 1 ∨ k = 2) {s₀ : State} (hp : APre e s₀) {s : State} {Q : Addr} {t : Nat} (ht0 : 0 < t) (ht : t < 16)
    (hrsi : s.gpr .rsi = Q) (hrdx : s.gpr .rdx = BitVec.ofNat 64 t) (hr15 : s.gpr .r15 = cx s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsrc : ∀ j < t, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 j) 1)
    (hdisj : ∀ j < t, (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint (sub s₀ 576 16)) :
    WP isa (padTail b k) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ ((bytesAt s.mem Q t ++ List.replicate (16 - t) 0) ++
          bytesAt s.mem (off (cx s₀) 592) (16 * k - 16))) := by
  rw [padTail_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel) (padZ_ok hp hr15 hwr) fun s₂ ⟨rcx₂, g₂, rd₂, wr₂, f₂, z₂⟩ mx₂ => ?_)
  have hd' : ∀ j < t, ∀ r ∈ [sub s₀ 576 16], (⟨Q + BitVec.ofNat 64 j, 1⟩ : Region).Disjoint r := by
    intro j hj r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdisj j hj
  have src₂ : ∀ j < t, s₂.mem (Q + BitVec.ofNat 64 j) = s.mem (Q + BitVec.ofNat 64 j) := fun j hj =>
    f₂ _ fun r hr hc => hd' j hj r hr _ (by simp only [Region.Contains]; rw [BitVec.sub_self]; simp) hc
  refine WP.seq (WP.mono_mx (by decide +kernel) (Q := CpInv s₀ s₂ Q t) ?_ fun s₃ h₃ mx₃ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ i, n = t - i ∧ i < t ∧ CpInv s₀ s₂ Q i s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (eval .ne s' = some false ∧ CpInv s₀ s₂ Q t s') ∨ (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨i, rfl, hi, hI⟩
      refine WP.mono (copy_step hp ht (by rw [g₂ _ (by decide) (by decide), hrsi])
        (by rw [g₂ _ (by decide) (by decide), hrdx]) (by rw [g₂ _ (by decide) (by decide), hr15])
        (by rw [wr₂, hwr]) (by rw [rd₂, wr₂]; exact hsrc) hd' hi hI) fun s' ⟨h', hz⟩ => ?_
      by_cases hl : i + 1 = t
      · exact .inl ⟨by simp [eval, hz, hl], hl ▸ h'⟩
      · exact .inr ⟨by simp [eval, hz, hl], t - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep t s₂ ⟨0, by simp, ht0, ⟨by rw [rcx₂]; rfl, fun _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _, fun j hj => by simp [z₂ j hj]⟩⟩
  have g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [h₃.keep r h₁ h₂, g₂ r h₁ h₂]
  refine WP.seq (WP.block_append (WP.mono_mx (by decide +kernel) (ptr_ok .rdi .r15 (k := 448) (by lit_omega) s₃)
    fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_))
  refine WP.block_append (WP.mono_mx (by decide +kernel) (ptr_ok .rsi .r15 (k := 576) (by lit_omega) s₄)
    fun s₅ ⟨e5, g₅, rd₅, wr₅, m₅⟩ mx₅ => ?_)
  refine WP.mono_mx (by rcases hk with rfl | rfl <;> decide +kernel) (mov32_rdx_ok (BitVec.ofNat 32 k) s₅) fun s₆ ⟨e6, g₆, rd₆, wr₆, m₆⟩ mx₆ => ?_
  have r15₃ : s₃.gpr .r15 = cx s₀ := by rw [g₃ _ (by decide) (by decide), hr15]
  have rdi₆ : s₆.gpr .rdi = off (cx s₀) 448 := by rw [g₆ _ (by decide), g₅ _ (by decide), e4, r15₃]
  have rsi₆ : s₆.gpr .rsi = off (cx s₀) 576 := by rw [g₆ _ (by decide), e5, g₄ _ (by decide), r15₃]
  have rdx₆ : s₆.gpr .rdx = BitVec.ofNat 64 k := by rw [e6]; rcases hk with rfl | rfl <;> rfl
  have g₆' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s₆.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₆ r h₅, g₅ r h₄, g₄ r h₃, g₃ r h₁ h₂]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsp]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, h₃.rd, rd₂, hrd]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, h₃.wr, wr₂, hwr]
  have mm₆ : s₆.mem = s₃.mem := by rw [m₆, m₅, m₄]
  have hk2 : k ≤ 2 := by omega
  refine WP.seq (WP.mono (blocks_call (n := k) rdi₆ rsi₆ rdx₆ (by lit_omega)
    (sub_disj s₀ (b := 576) (m := 16 * k) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (by rw [rsp₆]; exact hp.stk_sub (by lit_omega)) (by rw [rsp₆]; exact hp.stk_sub (by lit_omega))
    (Covers.right (covers_sub hp wr₆' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨576, rfl, show 576 + 16 * k ≤ 1696 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩)))
    (covers_sub hp wr₆' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩))
    b) fun s₇ ⟨rd₇, wr₇, cs₇, f₇, rdi₇, repr₇, mx₇⟩ => ?_)
  rw [rsp₆] at f₇
  refine WP.mono_mx (by decide +kernel) (anchor_ok .rdi (k := 448) (by lit_omega) s₇)
    fun s₈ ⟨e8, g₈, rd₈, wr₈, m₈⟩ mx₈ => ?_
  have hframe : Frame (macR s₀) s.mem s₆.mem := by
    rw [mm₆]
    exact (frame_mac (by lit_omega) (by lit_omega) f₂).trans (frame_mac (by lit_omega) (by lit_omega) h₃.frame)
  refine ⟨fun r hr => ?_, by rw [rd₈, rd₇, rd₆', hrd], by rw [wr₈, wr₇, wr₆', hwr], ?_,
    by rw [mx₈, mx₇, mx₆, mx₅, mx₄, mx₃, mx₂], fun key msg hr => ?_⟩
  · by_cases h15 : r = .r15
    · subst h15; rw [e8, rdi₇, off_sub, hr15]
    · have h' := calleeSaved_ne hr
      rw [g₈ r h15, cs₇ r hr, g₆' r h'.1 h'.2.1 h'.2.2.2.2 h'.2.2.2.1 h'.2.2.1]
  · rw [m₈]; exact hframe.trans (frame_mac' (by lit_omega) (by lit_omega) f₇)
  · rw [m₈]
    have f26 : Frame [sub s₀ 576 16] s.mem s₆.mem := by rw [mm₆]; exact f₂.trans h₃.frame
    have hr₆ : Repr s₆.mem (off (cx s₀) 448) key msg := Repr.frame f26 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr
    have hb16 : bytesAt s₆.mem (off (cx s₀) (576 : Nat)) 16 = bytesAt s.mem Q t ++ List.replicate (16 - t) 0 := by
        rw [mm₆, padded_bytes ht h₃.buf]
        congr 1
        simp only [bytesAt]
        apply List.map_congr_left
        intro j hj
        exact src₂ j (List.mem_range.mp hj)
    have hlen : bytesAt s₆.mem (off (cx s₀) 592) (16 * k - 16) = bytesAt s.mem (off (cx s₀) 592) (16 * k - 16) := by
      rw [mm₆]
      refine bytesAt_frame (f₂.trans h₃.frame) (fun r hr => ?_) (by lit_omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    have hb : bytesAt s₆.mem (off (cx s₀) (576 : Nat)) (16 * k) =
        (bytesAt s.mem Q t ++ List.replicate (16 - t) 0) ++ bytesAt s.mem (off (cx s₀) 592) (16 * k - 16) := by
      have e := VG.Proof.Poly1305.bytesAt_add s₆.mem (off (cx s₀) 576) 16 (16 * k - 16)
      rw [show 16 + (16 * k - 16) = 16 * k by omega] at e
      rw [e, hb16, show off (cx s₀) 576 + BitVec.ofNat 64 16 = off (cx s₀) 592 by
        rw [off_eq, off_eq, BitVec.add_assoc, ← BitVec.ofNat_add], hlen]
    have := repr₇ key msg hr₆
    rwa [hb] at this

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by lit_omega), Nat.shiftRight_eq_div_pow]

theorem and15_ofNat {len : Nat} (h : len < 2 ^ 64) : BitVec.ofNat 64 len &&& 15 = BitVec.ofNat 64 (len % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_ofNat_lt h, toNat_ofNat_lt (by lit_omega),
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem self_contains (a : Addr) : (⟨a, 1⟩ : Region).Contains a 1 := by
  simp only [Region.Contains]; rw [BitVec.sub_self]; simp

/-- What absorbing the blocks of `n` bytes leaves. -/
def MacPost (s₀ s : State) (bs : List Byte) (s' : State) : Prop :=
  (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
    Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
    ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → Repr s'.mem (off (cx s₀) 448) key (msg ++ bs)

theorem wholeBlocks_eq (b : Impl.Poly1305.X86_64.Blocks) (p n : Reg) : wholeBlocks b p n =
    .seq (.block (ptr .rdi .r15 448 ++ ([.mov .rsi (.reg p), .mov .rdx (.reg n), .shift .shr .rdx 4] : List Instr)))
      (.ite .e (.block []) (.seq (.call b.name b.code) (.block (anchor .rdi 448)))) := rfl

/-- The whole blocks of the `len` bytes at `P` (in `p` and `n`) absorbed, with
no call if there are none. -/
theorem wholeBlocks_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre e s₀) {p n : Reg}
    (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (wholeBlocks b p n) s (MacPost s₀ s (bytesAt s.mem P (16 * (len / 16)))) := by
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  rw [wholeBlocks_eq]
  refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel) (macA_ok hr s)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, zf₁, g₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have g₁' : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r := fun r h =>
    g₁ r (calleeSaved_ne h).2.2.2.2 (calleeSaved_ne h).2.2.2.1 (calleeSaved_ne h).2.2.1
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁' _ (by simp [calleeSaved]), hrsp]
  have hk : 16 * (len / 16) ≤ len := Nat.mul_div_le _ _
  have z : s₁.zf = some (decide (len / 16 = 0)) := by
    rw [zf₁, hn, shr4_ofNat hlt]
    congr 1
    by_cases h0 : len / 16 = 0
    · simp [h0]
    · have : BitVec.ofNat 64 (len / 16) ≠ 0 := by
        intro he; have := congrArg BitVec.toNat he; rw [toNat_ofNat_lt (by lit_omega)] at this; exact h0 this
      rw [decide_eq_false h0, beq_eq_false_iff_ne]; exact this
  refine WP.ite (decide (len / 16 = 0)) (by simp only [eval, z]) (fun h => ?_) (fun h => ?_)
  · have h0 : len / 16 = 0 := by simpa using h
    refine WP.block_nil ⟨g₁', rd₁, wr₁, by rw [m₁]; exact Frame.refl _ _, by rw [mx₁], fun key msg hr => ?_⟩
    rw [m₁, h0, Nat.mul_zero]
    simpa [bytesAt] using hr
  refine WP.seq (WP.mono (blocks_call (P := off (cx s₀) 448) (p := P) (n := len / 16)
    (by rw [rdi₁, hr15]) (by rw [rsi₁, hP]) (by rw [rdx₁, hn, shr4_ofNat hlt]) (by lit_omega)
    ((hcP.sub_left (sub_ctx s₀ (by lit_omega))).sub_right (Region.sub_prefix hk))
    (by have := hs.wrap; omega)
    (by rw [rsp₁]; exact hp.stk_sub (by lit_omega))
    (by rw [rsp₁]; exact hs.stk.sub_right (Region.sub_prefix hk))
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [rd₁, wr₁, hrd, hwr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
      · refine Covers.right (covers_sub hp (by rw [wr₁, hwr]) [sub s₀ 448 128] (fun r hr => ?_)) a w
          ⟨_, List.mem_singleton_self _, hc⟩
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩)
    (covers_sub hp (by rw [wr₁, hwr]) _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩))
    b) fun s₂ ⟨rd₂, wr₂, cs₂, f₂, rdi₂, repr₂, mx₂⟩ => ?_)
  rw [rsp₁, m₁] at f₂
  rw [m₁] at repr₂
  refine WP.mono_mx (by decide +kernel) (anchor_ok .rdi (k := 448) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_
  refine ⟨fun r hr => ?_, by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁],
    by rw [m₃]; exact frame_mac' (by lit_omega) (by lit_omega) f₂, by rw [mx₃, mx₂, mx₁],
    fun key msg hr => by rw [m₃]; exact repr₂ key msg hr⟩
  by_cases h15 : r = .r15
  · subst h15; rw [e3, rdi₂, off_sub, hr15]
  · rw [g₃ r h15, cs₂ r hr, g₁' r hr]

/-- After the whole blocks: `rdx` the number of bytes left, and `rsi` at them. -/
theorem macTail_ok {p n : Reg} (hr : MacRegs p n) {len : Nat} (hlt : len < 2 ^ 64)
    {s : State} (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (.block [.mov .rdx (.reg n), .alu .and .rdx (.imm 15)]) s fun s' =>
      s'.gpr .rdx = BitVec.ofNat 64 (len % 16) ∧ s'.zf = some (decide (len % 16 = 0)) ∧
      (∀ q, q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  refine WP.mono (macC_ok hr s) fun s' ⟨rdx', zf', g', rd', wr', m'⟩ => ⟨by rw [rdx', hn, and15_ofNat hlt], ?_,
    g', rd', wr', m'⟩
  rw [zf', hn, and15_ofNat hlt]
  congr 1
  by_cases h0 : len % 16 = 0
  · simp [h0]
  · have : BitVec.ofNat 64 (len % 16) ≠ 0 := by
      intro he; have := congrArg BitVec.toNat he; rw [toNat_ofNat_lt (by lit_omega)] at this; exact h0 this
    rw [decide_eq_false h0, beq_eq_false_iff_ne]; exact this

/-- The last `len mod 16` bytes at `P` (in `p` and `n`), padded, with the `k - 1` blocks
at `ctx + 592`, absorbed, from the state after the whole blocks. -/
theorem macRest_ok (b : Impl.Poly1305.X86_64.Blocks) {k : Nat} (hk : k = 1 ∨ k = 2) {s₀ : State}
    (hp : APre e s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat} (hs : Src s₀ P len)
    (h0 : len % 16 ≠ 0) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (len % 16)) :
    WP isa (.seq (.block (tailPtr p n)) (padTail b k)) s
      (MacPost s₀ s ((bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) ++
        List.replicate (16 - len % 16) 0) ++ bytesAt s.mem (off (cx s₀) 592) (16 * k - 16))) := by
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  have hp15 : p ≠ .r15 := by rcases hr.1 with rfl | rfl <;> decide
  refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel) (macD_ok hr s)
    fun s₄ ⟨rsi₄, g₄, rd₄, wr₄, m₄⟩ mx₄ => ?_)
  have g₄' : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r h => by
    rw [g₄ r (calleeSaved_ne h).2.2.2.1]
  have hQ : s₄.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) := by
    rw [rsi₄, hn, hrdx, hP]
    have e : len = 16 * (len / 16) + len % 16 := (Nat.div_add_mod _ _).symm
    have e' : BitVec.ofNat 64 len = BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 (len % 16) := by
      conv => lhs; rw [e]
      rw [BitVec.ofNat_add]
    rw [e', BitVec.add_sub_cancel, BitVec.add_comm]
  have hsrc : ∀ j < len % 16, InRegions (s₄.rd ++ s₄.wr)
      (P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hs.cov_sub (a := 16 * (len / 16) + j) (n := 1) (by lit_omega) (by rw [rd₄, hrd])
      (by rw [wr₄, hwr]) _ _ ⟨_, List.mem_singleton_self _, self_contains _⟩
  have hdj : ∀ j < len % 16, (⟨P + BitVec.ofNat 64 (16 * (len / 16)) + BitVec.ofNat 64 j, 1⟩ :
      Region).Disjoint (sub s₀ 576 16) := fun j hj => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (Src.disj_sub (hcP.sub_left (sub_ctx s₀ (by lit_omega))) (a := 16 * (len / 16) + j) (n := 1)
      (by lit_omega)).symm
  refine WP.mono (padTail_ok b hk hp (Q := P + BitVec.ofNat 64 (16 * (len / 16))) (t := len % 16)
    (by lit_omega) (by lit_omega) hQ
    (by rw [g₄ _ (by decide), hrdx])
    (by rw [g₄ _ (by decide), hr15])
    (by rw [g₄' _ (by simp [calleeSaved]), hrsp]) (by rw [rd₄, hrd]) (by rw [wr₄, hwr])
    hsrc hdj) fun s₅ ⟨cs₅, rd₅, wr₅, f₅, mx₅, repr₅⟩ => ?_
  refine ⟨fun r h => by rw [cs₅ r h, g₄' r h], by rw [rd₅, rd₄], by rw [wr₅, wr₄],
    by rw [← m₄]; exact f₅, by rw [mx₅, mx₄], fun key msg hr => ?_⟩
  have := repr₅ key msg (by rw [m₄]; exact hr)
  rwa [m₄] at this

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, absorbed. -/
theorem macPad_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre e s₀) {p n : Reg} (hr : MacRegs p n) {P : Addr} {len : Nat}
    (hs : Src s₀ P len) {s : State} (hr15 : s.gpr .r15 = cx s₀) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPad b p n) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len))) := by
  have hpc : p ∈ calleeSaved := by rcases hr.1 with rfl | rfl <;> simp [calleeSaved]
  have hnc : n ∈ calleeSaved := by rcases hr.2 with rfl | rfl <;> simp [calleeSaved]
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  refine WP.seq (WP.mono (wholeBlocks_ok b hp hr hs hr15 hrsp hrd hwr hP hn)
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, repr₂⟩ => ?_)
  refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel)
    (macTail_ok hr hlt (by rw [cs₂ n hnc, hn]))
    fun s₃ ⟨rdx₃, zf₃, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_)
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r h => by
    rw [g₃ r (calleeSaved_ne h).2.2.1, cs₂ r h]
  have hdisjP : ∀ r ∈ macR s₀, (⟨P, len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hcP.sub_left (sub_ctx s₀ (by lit_omega))).symm
    · exact hs.stk.symm
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  refine WP.ite (decide (len % 16 = 0)) (by simp only [eval, zf₃]) (fun h => ?_) (fun h => ?_)
  · have h0 : len % 16 = 0 := by simpa using h
    refine WP.block_nil ⟨cs₃, by rw [rd₃, rd₂], by rw [wr₃, wr₂], by rw [m₃]; exact f₂,
      by rw [mx₃, mx₂], fun key msg hr => ?_⟩
    rw [m₃]
    have := repr₂ key msg hr
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using h
    refine WP.mono (macRest_ok b (k := 1) (.inl rfl) hp hr hs h0
      (by rw [cs₃ _ (by simp [calleeSaved]), hr15])
      (by rw [cs₃ _ (by simp [calleeSaved]), hrsp]) (by rw [rd₃, rd₂, hrd]) (by rw [wr₃, wr₂, hwr])
      (by rw [cs₃ p hpc, hP]) (by rw [cs₃ n hnc, hn]) rdx₃) fun s₅ ⟨cs₅, rd₅, wr₅, f₅, mx₅, repr₅⟩ => ?_
    refine ⟨fun r h => by rw [cs₅ r h, cs₃ r h], by rw [rd₅, rd₃, rd₂], by rw [wr₅, wr₃, wr₂],
      f₂.trans (by rw [← m₃]; exact f₅), by rw [mx₅, mx₃, mx₂], fun key msg hr => ?_⟩
    have := repr₅ key _ (by rw [m₃]; exact repr₂ key msg hr)
    rw [m₃, bytesAt_frame f₂ (fun r hr => (hdisjP r hr).sub_left
      (sub_off P (a := 16 * (len / 16)) (by lit_omega))) (by lit_omega)] at this
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by simp [pad16, hlen, h0],
      x_eq]
    simpa only [List.append_assoc, show 16 * 1 - 16 = 0 from rfl, bytesAt, List.range_zero, List.map_nil,
      List.append_nil] using this

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: the other parts

The lengths block, the encryption, absorbing the lengths, the tag, comparing
tags, and restoring the registers.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

theorem calleeSaved_rsp : Reg.rsp ∈ calleeSaved := by simp [calleeSaved]

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the working space, the data and the stack. -/
theorem Inv.step {s₀ s s' : State} (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 0 48).Disjoint r) : Inv s₀ s' where
  r15 := by rw [cs _ (by simp [calleeSaved]), h.r15]
  r14 := by rw [cs _ (by simp [calleeSaved]), h.r14]
  r13 := by rw [cs _ (by simp [calleeSaved]), h.r13]
  r12 := by rw [cs _ (by simp [calleeSaved]), h.r12]
  rsp := by rw [cs _ calleeSaved_rsp, h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  saved := h.saved.frame hf hsv
  frame := h.frame.trans (hf.sub hsub)

/-- `ctx[k, k + n)` in the working space. -/
theorem sub_work (s₀ : State) {k n : Nat} (h₁ : 0 ≤ k) (h₂ : k + n ≤ 1696) :
    ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (sub s₀ k n) r' :=
  ⟨workR s₀, by simp, sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩

theorem stk_work (s₀ : State) : ∃ r' ∈ [workR s₀, dR s₀, stkR s₀], Region.Sub (stkR s₀) r' :=
  ⟨stkR s₀, by simp, fun _ h => h⟩

theorem mac_inv {s₀ s s' : State} (hp : APre e s₀) (h : Inv s₀ s) (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame (macR s₀) s.mem s'.mem) : Inv s₀ s' :=
  h.step cs hrd hwr hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_work s₀ (by lit_omega) (by lit_omega)
      · exact stk_work s₀)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact (hp.stk_sub (by lit_omega)).symm)

/-! ## The lengths block -/

theorem bytesAt_16 (m : Mem) (p : Addr) :
    bytesAt m p 16 = leBytes 8 (m.readW p 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_leBytes_64,
    VG.Proof.Poly1305.bytesAt_leBytes_64, off_eq]

set_option simprocs false in
theorem lengths_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (hrbp : s.gpr .rbp = s₀.gpr .rcx) :
    WP isa (.block lengths) s fun s' => Inv s₀ s' ∧ (∀ r, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 592 16] s.mem s'.mem ∧
      bytesAt s'.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have o0 := hp.in_ctx (a := 592) (w := 8) (by lit_omega)
  have o1 := hp.in_ctx (a := 600) (w := 8) (by lit_omega)
  rw [← h.wr] at o0 o1
  simp only [off] at o0 o1
  apply WP.of_runBlock
  simp (config := {decide := true}) only [lengths, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, h.r15, o0, o1, ite_true, Option.some.injEq, exists_eq_left']
  have hf : Frame [sub s₀ 592 16] s.mem ((s.mem.writeW (off (cx s₀) 592) (s.gpr .rbp)).writeW
      (off (cx s₀) 600) (s.gpr .r13)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega))
      |>.writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine ⟨h.step (fun _ _ => rfl) rfl rfl hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    fun _ => trivial, hf, ?_⟩
  rw [bytesAt_16, off_off, show 592 + 8 = 600 from rfl, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64, hrbp, h.r13]

/-! ## Restoring the registers -/

set_option simprocs false in
/-- The loads of the saved registers, through `r15` (`r15` last). -/
theorem restoreLoads_ok {s₀ : State} (hp : APre e s₀) {s : State} (hr15 : s.gpr .r15 = cx s₀)
    (hsv : Saved s₀ s.mem) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restoreLoads) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .rax = s.gpr .rax ∧ s'.mem = s.mem := by
  have i : ∀ d, d + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := by
    intro d h₂
    rw [hrd, hwr]; exact hp.in_ctx' h₂
  have i0 := i 0 (by lit_omega)
  have i1 := i 8 (by lit_omega)
  have i2 := i 16 (by lit_omega)
  have i3 := i 24 (by lit_omega)
  have i4 := i 32 (by lit_omega)
  have i5 := i 40 (by lit_omega)
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := hsv
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restoreLoads, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, ea_at, readSrc, State.load64, State.setReg, hr15, i0, i1, i2, i3, i4,
    i5, v0, v1, v2, v3, v4, v5, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_true, ite_false, hrsp]

theorem restore_ok {s₀ : State} (hp : APre e s₀) {s : State} (hrdi : s.gpr .rdi = off (cx s₀) 448)
    (hsv : Saved s₀ s.mem) (hrsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .rax = s.gpr .rax ∧ s'.mem = s.mem := by
  refine WP.block_append (WP.mono (anchor_ok .rdi (k := 448) (by lit_omega) s) fun s₁ ⟨e₁, g₁, rd₁, wr₁, m₁⟩ =>
    WP.mono (restoreLoads_ok hp (by rw [e₁, hrdi, off_sub]) (by rw [m₁]; exact hsv)
      (by rw [g₁ _ (by decide), hrsp]) (by rw [rd₁, hrd]) (by rw [wr₁, hwr]))
      fun s' ⟨cs', rax', m'⟩ => ⟨cs', by rw [rax', g₁ _ (by decide)], by rw [m', m₁]⟩)

/-! ## Comparing the tags -/

theorem bytesAt_8_eq {m : Mem} {p q : Addr} :
    bytesAt m p 8 = bytesAt m q 8 ↔ m.readW p 64 = m.readW q 64 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [← VG.Proof.Poly1305.leNum_bytesAt_64, ← VG.Proof.Poly1305.leNum_bytesAt_64, h]
  · intro h
    rw [VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, h]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (off p 8) 64 ^^^ m.readW (off q 8) 64)) = 0#64 ↔
      bytesAt m p 16 = bytesAt m q 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff, show 16 = 8 + 8 from rfl,
    VG.Proof.Poly1305.bytesAt_add, VG.Proof.Poly1305.bytesAt_add, ← off_eq, ← off_eq, ← bytesAt_8_eq,
    ← bytesAt_8_eq]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro h
    exact List.append_inj h (by rw [VG.Proof.Poly1305.length_bytesAt, VG.Proof.Poly1305.length_bytesAt])

theorem ea_disp (s : State) (b : Reg) (d : Int) :
    s.ea { base := b, disp := d } = s.gpr b + BitVec.ofInt 64 d := rfl

theorem off_neg {p : Addr} {a d : Nat} (h : d ≤ a) :
    off p a + BitVec.ofInt 64 (-(d : Int)) = off p (a - d) := by
  rw [off_eq, off_eq]
  have : BitVec.ofInt 64 (-(d : Int)) = -BitVec.ofNat 64 d := by
    rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [this, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat h]

set_option simprocs false in
theorem compare_ok {s₀ : State} (hp : APre false s₀) {s : State} (hrcx : s.gpr .rcx = off (cx s₀) 48)
    (hr12 : s.gpr .r12 = tp s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block compare) s fun s' =>
      (s'.gpr .rax).setWidth 32 =
        (if bytesAt s.mem (off (cx s₀) 48) 16 = bytesAt s.mem (tp s₀) 16 then 1 else 0) ∧
      (∀ q, q ≠ .rax → q ≠ .rdx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 : off (off (cx s₀) 48) 0 = off (cx s₀) 48 := by rw [off_off]
  have e1 : off (tp s₀) 0 = tp s₀ := by rw [off_eq]; exact BitVec.add_zero _
  have i : ∀ a, a + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) 8 := fun a h => by
    rw [hrd, hwr]; exact hp.in_ctx' h
  have it : ∀ a, a + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (off (tp s₀) a) 8 := fun a h => by
    rw [hrd, hwr]
    exact ⟨tR s₀, by simp [hp.t_rd], by rw [off_eq]; exact Offset.contains_base _ h (by lit_omega)⟩
  have i0 := i 48 (by lit_omega)
  have i1 := it 0 (by lit_omega)
  rw [e1] at i1
  have i2 : InRegions (s.rd ++ s.wr) (off (off (cx s₀) 48) 8) 8 := by rw [off_off]; exact i 56 (by lit_omega)
  have i3 := it 8 (by lit_omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.ChaCha20Poly1305.X86_64.compare, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, readSrc32, execAlu, execAlu32, arithFlags, State.load64, State.setReg, State.setReg32,
    State.setFlags, hrcx, hr12, e0, e1, i0, i1, i2, i3, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se1']
  refine ⟨?_, fun q h₁ h₂ => by simp [h₁, h₂], trivial⟩
  have ht := tag_eq s.mem (off (cx s₀) 48) (tp s₀)
  generalize ((s.mem.readW (off (cx s₀) 48) 64 ^^^ s.mem.readW (tp s₀) 64) |||
    (s.mem.readW (off (off (cx s₀) 48) 8) 64 ^^^ s.mem.readW (off (tp s₀) 8) 64)) = x at ht ⊢
  by_cases hb : bytesAt s.mem (off (cx s₀) 48) 16 = bytesAt s.mem (tp s₀) 16
  · rw [ite_eq_left hb, ht.mpr hb]; decide
  · have hx : ¬ x.toNat < 1 := fun h => hb (ht.mp (BitVec.eq_of_toNat_eq (by simp; omega)))
    rw [ite_eq_right hb]; simp [hx]

/-! ## Encrypting -/

/-- Setting the block counter in memory. -/
theorem stateAt_ctr (m : Mem) (c : Addr) :
    stateAt (m.writeW (off c 112) (1 : BitVec 32)) (off c 64) = (stateAt m (off c 64)).set 12 1 := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_set, Vector.getElem_ofFn]
  rw [show off c 64 + BitVec.ofNat 64 (4 * i) = off c (64 + 4 * i) by
    simp only [off_eq, BitVec.ofNat_add, BitVec.add_assoc]]
  by_cases h : 12 = i
  · subst h; simp only [ite_true]; exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW32_off m c 1 (by lit_omega) (by lit_omega) (by lit_omega)

set_option simprocs false in
theorem cryptA_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block cryptArgs) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s'.gpr .rdi = off (cx s₀) 64 ∧
      s'.gpr .rsi = dp s₀ ∧ s'.gpr .rdx = s₀.gpr .r9 ∧ s'.gpr .rcx = off (cx s₀) 128 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := hp.in_ctx (a := 112) (w := 4) (by lit_omega)
  rw [← h.wr] at o
  simp only [off] at o
  apply WP.of_runBlock
  simp (config := {decide := true}) only [cryptArgs, ptr, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, ea_at, readSrc, readSrc32, execAlu, arithFlags, State.store32, State.setReg,
    State.setReg32, State.setFlags, h.r15, h.r14, h.r13, o, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se_ofNat (show 64 < 2 ^ 31 by omega),
    se_ofNat (show 128 < 2 ^ 31 by omega), BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  refine ⟨trivial, by rw [off_eq], trivial, trivial, by rw [off_eq], fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem hL (s₀ : State) : s₀.gpr .r9 = BitVec.ofNat 64 (L s₀) := by simp [L]

/-- The arguments of `vg_chacha20_xor`, as `cryptArgs` sets them up. -/
structure XArgs (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = off (cx s₀) 64
  rsi : s.gpr .rsi = dp s₀
  rdx : s.gpr .rdx = s₀.gpr .r9
  rcx : s.gpr .rcx = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  wr : s.wr = s₀.wr

theorem XArgs.of {s₀ s s' : State} (h : Inv s₀ s) (rdi : s'.gpr .rdi = off (cx s₀) 64) (rsi : s'.gpr .rsi = dp s₀)
    (rdx : s'.gpr .rdx = s₀.gpr .r9) (rcx : s'.gpr .rcx = off (cx s₀) 128)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (wr : s'.wr = s.wr) : XArgs s₀ s' :=
  ⟨rdi, rsi, rdx, rcx, by rw [cs _ calleeSaved_rsp, h.rsp], by rw [cs _ (by simp [calleeSaved]), h.r13],
    by rw [cs _ (by simp [calleeSaved]), h.r14], by rw [cs _ (by simp [calleeSaved]), h.r12],
    by rw [wr, h.wr]⟩

theorem cryptArgs_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block cryptArgs) s (XArgs s₀) :=
  WP.mono (cryptA_ok hp h) fun _ ⟨_, rdi, rsi, rdx, rcx, cs, _, wr⟩ => XArgs.of h rdi rsi rdx rcx cs wr

section
variable {s₀ : State} (hp : APre e s₀) {s : State} (h : XArgs s₀ s)
include hp h

theorem XArgs.hw : Covers [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩] s.wr := by
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 64, by simp [off_eq], by show 64 + 64 ≤ 1696; omega⟩
  · exact ⟨dR s₀, by rw [h.wr]; exact hp.d_wr, 0, by simp, by simp⟩
  · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 128, by simp [off_eq], by show 128 + 320 ≤ 1696; omega⟩

/-- The precondition of the implementation `v` of `vg_chacha20_xor`. -/
theorem XArgs.pre (v : Proof.ChaCha20.X86_64.XorImpl) :
    (Proof.ChaCha20.xorStack v.stack).pre
      (s.callEntry.withRegions [] [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩]) :=
  xor_pre v h.rdi h.rsi (by rw [h.rdx]; exact hL s₀) h.rcx (s₀.gpr .r9).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) hp.wrap_d
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))

/-- The call of the implementation `v` of `vg_chacha20_xor`. -/
theorem XArgs.call (v : Proof.ChaCha20.X86_64.XorImpl) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨off (cx s₀) 64, 64⟩, ⟨dp s₀, L s₀⟩, ⟨off (cx s₀) 128, 320⟩, stkR s₀] s.mem s'.mem →
      s'.gpr .rsi = off (cx s₀) 128 →
      Spec.ChaCha20.bytesAt s'.mem (dp s₀) (L s₀) = List.zipWith (· ^^^ ·)
        (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)) (keystream (stateAt s.mem (off (cx s₀) 64)) (L s₀)) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q :=
  xor_call v h.rdi h.rsi (by rw [h.rdx]; exact hL s₀) h.rcx (s₀.gpr .r9).isLt
    (hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)))
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    (hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))) hp.wrap_d
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_d)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) ((Covers.right (h.hw hp))) (h.hw hp)
    fun s' rd wr cs f rsi data => hQ s' rd wr cs (by rw [h.rsp] at f; exact f) rsi data

end

theorem cmpFold_ok {fold : Nat} (hf : fold + 1 < 2 ^ 31) {s₀ : State} {s : State}
    (hr13 : s.gpr .r13 = s₀.gpr .r9) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (fold + 1)))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      s'.cf = some (decide (L s₀ < fold + 1)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left', se_ofNat hf]
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [hr13, toNat_ofNat_lt (by lit_omega)]

/-- After the data is encrypted (or decrypted), before the keystream is wiped. -/
structure Crypted (s₀ s : State) (s' : State) : Prop where
  rsi : s'.gpr .rsi = off (cx s₀) 128
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s'.mem
  data : bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀))

theorem C1_eq : ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr) =
    ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr) := rfl

/-- At most `fold` bytes: the keystream from the prologue XORed into them. -/
theorem cryptSmall_ok {fold : Nat} (hf : fold ≤ 960) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hle : L s₀ ≤ fold)
    (hks : ∀ k < mOf fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (Spec.ChaCha20.keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0) :
    WP isa (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX .r14) (.block (ptr .rsi .r15 128)))) s (Crypted s₀ s) := by
  have hL9 := (s₀.gpr .r9).isLt
  have hm : mOf fold (L s₀) = L s₀ := by simp only [mOf, hle, ite_true]
  refine WP.seq (WP.block_append (WP.mono (ptr_ok .rsi .r15 (k := 736) (by lit_omega) s)
    fun s₁ ⟨e1, g₁, rd₁, wr₁, m₁⟩ => ?_))
  refine WP.mono (Q := fun (s' : State) => s'.gpr .rdx = s₀.gpr .r9 ∧ (∀ q, q ≠ .rdx → s'.gpr q = s₁.gpr q) ∧
      s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧ s'.mem = s₁.mem) ?_ fun s₂ ⟨d₂, g₂, rd₂, wr₂, m₂⟩ => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, Option.map_some,
      Option.some.injEq, exists_eq_left', ite_true]
    exact ⟨by rw [g₁ _ (by decide), h.r13], fun q hq => by simp [hq], trivial, trivial, trivial⟩
  have rsi₂ : s₂.gpr .rsi = off (cx s₀) 736 := by rw [g₂ _ (by decide), e1, h.r15]
  have r14₂ : s₂.gpr .r14 = dp s₀ := by rw [g₂ _ (by decide), g₁ _ (by decide), h.r14]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁, h.wr]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁, h.rd]
  have dB : (dR s₀).Disjoint ⟨off (cx s₀) 736, L s₀⟩ :=
    hp.c_d.symm.sub_right (sub_ctx s₀ (k := 736) (n := L s₀) (by lit_omega))
  refine WP.seq (WP.mono (XorBufX.xorBufX_ok (d := .r14) (by decide)
    r14₂ rsi₂ (by rw [d₂]; exact hL s₀) hL9 dB
    ⟨dR s₀, by rw [wr₂']; exact hp.d_wr, Region.contains_self _ _⟩
    ⟨ctxR s₀, by rw [rd₂', wr₂']; simp [hp.ctx_wr], by
      rw [off_eq]; exact Offset.contains_base _ (show 736 + L s₀ ≤ 1696 by omega) (by lit_omega)⟩)
    fun s₃ h₃ => ?_)
  refine WP.mono (ptr_ok .rsi .r15 (k := 128) (by lit_omega) s₃) fun s₄ ⟨e4, g₄, rd₄, wr₄, m₄⟩ => ?_
  have r15₃ : s₃.gpr .r15 = cx s₀ := by
    rw [h₃.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide),
      g₁ _ (by decide), h.r15]
  refine ⟨by rw [e4, r15₃], fun r hr h15 => ?_, by rw [rd₄, h₃.rd, rd₂, rd₁], by rw [wr₄, h₃.wr, wr₂, wr₁],
    ?_, ?_⟩
  · have h' := calleeSaved_ne hr
    rw [g₄ r h'.2.2.2.1, h₃.keep r h'.1 (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h'.2.1 h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2,
      g₂ r h'.2.2.1, g₁ r h'.2.2.2.1]
  · rw [m₄, ← m₁, ← m₂]
    exact h₃.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩
  · rw [m₄, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]
    apply VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _)
    intro k hk
    rw [h₃.data k hk, m₂, m₁, show off (cx s₀) 736 + BitVec.ofNat 64 k = off (cx s₀) (736 + k) by
      rw [off_eq, off_eq, BitVec.ofNat_add, BitVec.add_assoc], hks k (by rw [hm]; exact hk)]

/-- More than `fold` bytes: from counter 1, by the implementation `v` of `vg_chacha20_xor`. -/
theorem cryptBig_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa (.seq (.block cryptArgs) (.call v.callee.name v.callee.code)) s (Crypted s₀ s) := by
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, rdi₁, rsi₁, rdx₁, rcx₁, cs₁, rd₁, wr₁⟩ => ?_)
  refine (XArgs.of h rdi₁ rsi₁ rdx₁ rcx₁ cs₁ wr₁).call hp v fun s₂ rd₂ wr₂ cs₂ f₂ rsi₂ data₂ => ?_
  have f1 : Frame [sub s₀ 64 64] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega))
  refine ⟨rsi₂, fun r hr _ => by rw [cs₂ r hr, cs₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_, ?_⟩
  · refine (f1.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame f1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt (s₀.gpr .r9).isLt)
    have st₁ : stateAt s₁.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
      rw [m₁, stateAt_ctr, hst, set12_initState]
    rw [← bytesAt_eq, data₂, st₁, bytesAt_eq, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-- The data encrypted (or decrypted), by any implementation `v` of
`vg_chacha20_xor`, and the keystream wiped. -/
theorem crypt_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    (hks : ∀ k < mOf v.callee.fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0) :
    WP isa (crypt v.callee) s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame [sub s₀ 64 384, sub s₀ 672 1024, dR s₀, stkR s₀] s.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hfl := v.fold_le
  have hL9 := (s₀.gpr .r9).isLt
  have hm := mOf_le v.callee.fold (L s₀)
  unfold crypt
  refine WP.seq (WP.mono (cmpFold_ok (fold := v.callee.fold) (by lit_omega) h.r13)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ => ?_)
  have h₁ : Inv s₀ s₁ := h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine WP.seq (WP.mono (Q := Crypted s₀ s₁) ?_ fun s₂ c₂ => ?_)
  · refine WP.ite (decide (L s₀ < v.callee.fold + 1)) (by simp [eval, c₁]) (fun hc => ?_) (fun _ => ?_)
    · simp only [decide_eq_true_eq] at hc
      exact cryptSmall_ok hfl hp h₁ (by omega) (by rw [m₁]; exact hks)
    · exact cryptBig_ok v hp h₁ (by rw [m₁]; exact hst)
  refine WP.seq (WP.mono (anchor_ok .rsi (k := 128) (by lit_omega) s₂) fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ => ?_)
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, c₂.rsi, off_sub, h.r15]
    · rw [g₃ r h15, c₂.cs r hr h15, g₁]
  have i₃ : Inv s₀ s₃ := h.step cs₃ (by rw [rd₃, c₂.rd, rd₁]) (by rw [wr₃, c₂.wr, wr₁])
    (by rw [m₃, ← m₁]; exact c₂.frame) (fun r hr => by
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
  -- The keystream wiped.
  refine WP.seq (WP.mono (foldM_ok (fold := v.callee.fold) (len := L s₀) (by lit_omega) hL9
    (by rw [i₃.r13]; exact hL s₀)) fun s₄ ⟨d₄, g₄, rd₄, wr₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (add64_ok (n := mOf v.callee.fold (L s₀)) d₄) fun s₅ ⟨d₅, g₅, rd₅, wr₅, m₅⟩ => ?_)
  refine WP.mono (zeroKs_ok hp (n := 64 + mOf v.callee.fold (L s₀)) (by omega) (by lit_omega) d₅
    (by rw [g₅ _ (by decide), g₄ _ (by decide), i₃.r15]) (by rw [wr₅, wr₄, i₃.wr]))
    fun s₆ ⟨g₆, rd₆, wr₆, f₆, _⟩ => ?_
  have cs₆ : ∀ r ∈ calleeSaved, s₆.gpr r = s₃.gpr r := fun r hr => by
    have h' := calleeSaved_ne hr
    rw [g₆ r h'.1 h'.2.1, g₅ r h'.2.2.1, g₄ r h'.2.2.1]
  have f₅₆ : Frame [sub s₀ 672 1024] s₃.mem s₆.mem := by rw [← m₄, ← m₅]; exact f₆
  refine ⟨i₃.step cs₆ (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) f₅₆
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sub_work s₀ (by lit_omega) (by lit_omega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
    fun r hr => by rw [cs₆ r hr, cs₃ r hr], ?_, ?_⟩
  · have fc : Frame [sub s₀ 64 384, dR s₀, stkR s₀] s.mem s₃.mem := by rw [m₃, ← m₁]; exact c₂.frame
    refine (fc.sub fun r hr => ?_).trans (f₅₆.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame f₅₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).symm) (Nat.le_of_lt hL9), m₃, c₂.data, ← m₁]

/-! ## Absorbing the lengths and the tag -/

set_option simprocs false in
theorem ptrs_ok (k : Nat) (hk : k < 2 ^ 31) (v : BitVec 32) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 k ++ ([.mov32 .rdx (.imm v)] : List Instr))) s fun s' =>
      s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = off (s.gpr .r15) k ∧ s'.gpr .rdx = v.setWidth 64 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 448 < 2 ^ 31 by omega), se_ofNat hk]
  refine ⟨by rw [off_eq], by rw [off_eq], trivial, fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem absorbLengths_eq (b : Impl.Poly1305.X86_64.Blocks) : absorbLengths b =
    .seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 592 ++ ([.mov32 .rdx (.imm 1)] : List Instr)))
    (.seq (.call b.name b.code) (.block (anchor .rdi 448))) := rfl

/-- The lengths block absorbed. -/
theorem absorbLengths_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre e s₀) {s : State}
    (h : Inv s₀ s) :
    WP isa (absorbLengths b) s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 592) 16) := by
  rw [absorbLengths_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel) (ptrs_ok 592 (by lit_omega) 1 s)
    fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ mx₁ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  rw [h.r15] at rdi₁ rsi₁
  refine WP.seq (WP.mono (blocks_call (n := 1) rdi₁ rsi₁ (by rw [rdx₁]; rfl) (by lit_omega)
    (sub_disj s₀ (b := 592) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (by rw [rsp₁]; exact hp.stk_sub (by lit_omega)) (by rw [rsp₁]; exact hp.stk_sub (by lit_omega))
    (Covers.right (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨592, rfl, show 592 + 16 * 1 ≤ 1696 by omega⟩
      · exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩)))
    (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩))
    b) fun s₂ ⟨rd₂, wr₂, cs₂, f₂, rdi₂, repr₂, mx₂⟩ => ?_)
  rw [rsp₁, m₁] at f₂
  rw [m₁] at repr₂
  refine WP.mono_mx (by decide +kernel) (anchor_ok .rdi (k := 448) (by lit_omega) s₂)
    fun s₃ ⟨e3, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_
  have cs : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    by_cases h15 : r = .r15
    · subst h15; rw [e3, rdi₂, off_sub, h.r15]
    · rw [g₃ r h15, cs₂ r hr, cs₁ r hr]
  have hf : Frame (macR s₀) s.mem s₃.mem := by rw [m₃]; exact frame_mac' (by lit_omega) (by lit_omega) f₂
  exact ⟨mac_inv hp h cs (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) hf, cs, hf,
    by rw [mx₃, mx₂, mx₁], fun key msg hr => by rw [m₃]; exact repr₂ key msg hr⟩

set_option simprocs false in
theorem fptrs_ok (k : Nat) (hk : k < 2 ^ 31) (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ ptr .rdx .r15 k)) s fun s' =>
      s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = 0 ∧ s'.gpr .rdx = off (s.gpr .r15) k ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 448 < 2 ^ 31 by omega), se_ofNat hk]
  refine ⟨by rw [off_eq], trivial, by rw [off_eq], fun r hr => ?_, trivial⟩
  have := calleeSaved_ne hr
  simp [this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem finalizeTo_eq (out : Nat) : finalizeTo out =
    .seq (.block (ptr .rdi .r15 448 ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ ptr .rdx .r15 out))
      (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.X86_64.finalize) := rfl

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448 ∨ (576 ≤ out ∧ out + 16 ≤ 592)) :
    WP isa (finalizeTo out) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.gpr .rdi = off (cx s₀) 448 ∧ s'.gpr .rcx = off (cx s₀) out ∧
      Frame [sub s₀ 448 128, sub s₀ out 16, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (off (cx s₀) out) 16 = mac key msg := by
  rw [finalizeTo_eq]
  have ho : out + 16 ≤ 1696 := by omega
  refine WP.seq (WP.mono (fptrs_ok out (by lit_omega) s) fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  rw [h.r15] at rdi₁ rdx₁
  refine finalize_call rdi₁ rsi₁ rdx₁ (sub_disj s₀ (by lit_omega) (by lit_omega) ho)
    (by rw [rsp₁]; exact hp.below8_sub (by lit_omega)) (by rw [rsp₁]; exact hp.below8_sub ho)
    (Covers.right (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₁' _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 1696 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₃ rd₃ wr₃ cs₃ f₃ rdi₃ rcx₃ tag₃ => ?_
  rw [rsp₁, m₁] at f₃
  refine ⟨fun r hr => by rw [cs₃ r hr, cs₁ r hr], by rw [rd₃, rd₁], by rw [wr₃, wr₁], rdi₃, rcx₃,
    f₃.sub fun r hr => ?_, fun key msg hr => tag₃ key msg (by rw [m₁]; exact hr)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub s₀ 448 128, by simp, fun _ h => h⟩
  · exact ⟨sub s₀ out 16, by simp, fun _ h => h⟩
  · exact ⟨stkR s₀, by simp, below8_stk s₀⟩

theorem ftptrs_ok (s : State) :
    WP isa (.block (ptr .rdi .r15 448 ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ ([.mov .rdx (.reg .r12)] : List Instr))) s
      fun s' =>
      s'.gpr .rdi = off (s.gpr .r15) 448 ∧ s'.gpr .rsi = 0 ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [ptr, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, readSrc32, execAlu, arithFlags, State.setReg, State.setReg32, State.setFlags,
    reduceCtorEq, ↓reduceIte, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    se_ofNat (show 448 < 2 ^ 31 by omega)]
  refine ⟨by rw [off_eq], BitVec.setWidth_zero .., trivial, fun r hr => ?_, trivial, trivial, trivial⟩
  have := calleeSaved_ne hr
  simp [this.2.2.1, this.2.2.2.1, this.2.2.2.2]

theorem finalizeTag_eq : finalizeTag =
    .seq (.block (ptr .rdi .r15 448 ++ ([.mov32 .rsi (.imm 0)] : List Instr) ++ ([.mov .rdx (.reg .r12)] : List Instr)))
      (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.X86_64.finalize) := rfl

/-- The tag written to `tag`. -/
theorem finalizeTag_ok {s₀ : State} (hp : APre true s₀) {s : State} (h : Inv s₀ s) :
    WP isa finalizeTag s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.gpr .rdi = off (cx s₀) 448 ∧
      Frame [sub s₀ 448 128, tR s₀, stkR s₀] s.mem s'.mem ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg → bytesAt s'.mem (tp s₀) 16 = mac key msg := by
  rw [finalizeTag_eq]
  refine WP.seq (WP.mono (ftptrs_ok s) fun s₁ ⟨rdi₁, rsi₁, rdx₁, cs₁, rd₁, wr₁, m₁⟩ => ?_)
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [cs₁ _ calleeSaved_rsp, h.rsp]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, h.wr]
  rw [h.r15] at rdi₁
  rw [h.r12] at rdx₁
  have hw : Covers [sub s₀ 448 128, tR s₀] s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ctxR s₀, by rw [wr₁']; exact hp.ctx_wr, 448, by simp [off_eq], by show 448 + 128 ≤ 1696; omega⟩
    · exact ⟨tR s₀, by rw [wr₁']; exact hp.t_wr, 0, by simp, by simp⟩
  refine finalize_call rdi₁ rsi₁ rdx₁ (hp.c_t.sub_left (sub_ctx s₀ (by lit_omega)))
    (by rw [rsp₁]; exact hp.below8_sub (by lit_omega)) (by rw [rsp₁]; exact hp.stk_t.sub_left (below8_stk s₀))
    (Covers.right hw) hw
    fun s₃ rd₃ wr₃ cs₃ f₃ rdi₃ _ tag₃ => ?_
  rw [rsp₁, m₁] at f₃
  refine ⟨fun r hr => by rw [cs₃ r hr, cs₁ r hr], by rw [rd₃, rd₁], by rw [wr₃, wr₁], rdi₃,
    f₃.sub fun r hr => ?_, fun key msg hr => tag₃ key msg (by rw [m₁]; exact hr)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub s₀ 448 128, by simp, fun _ h => h⟩
  · exact ⟨tR s₀, by simp, fun _ h => h⟩
  · exact ⟨stkR s₀, by simp, below8_stk s₀⟩

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: correctness

`seal` and `open`, from their parts.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem APre.stk_d' {s₀ : State} (hp : APre e s₀) : (stkR s₀).Disjoint (dR s₀) := hp.stk_d
theorem APre.stk_a' {s₀ : State} (hp : APre e s₀) : (stkR s₀).Disjoint (aR s₀) := hp.stk_a
theorem APre.stk_t' {s₀ : State} (hp : APre e s₀) : (stkR s₀).Disjoint (tR s₀) := hp.stk_t

/-- That two of the regions the parts use are disjoint: parts of the context
at different offsets, the stack below the return address, and the data.
(Matching only reducibly, so that a lemma that does not apply fails fast.) -/
macro "rdisj" : tactic => `(tactic| first
  | with_reducible exact sub_disj _ (by lit_omega) (by lit_omega) (by lit_omega)
  | with_reducible exact (APre.stk_sub ‹APre _ _› (by lit_omega)).symm
  | with_reducible exact APre.stk_sub ‹APre _ _› (by lit_omega)
  | with_reducible exact (‹APre _ _›).c_d.sub_left (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).c_d.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (APre.stk_d' ‹APre _ _›).symm
  | with_reducible exact (‹APre _ _›).c_a.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (APre.stk_a' ‹APre _ _›).symm
  | with_reducible exact (‹APre _ _›).a_d
  | with_reducible exact (‹APre _ _›).ret_c.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).ret_d
  | with_reducible exact (‹APre _ _›).ret_t
  | with_reducible exact (‹APre _ _›).c_t.sub_left (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).c_t.symm.sub_right (sub_ctx _ (by lit_omega))
  | with_reducible exact (‹APre _ _›).d_t
  | with_reducible exact (‹APre _ _›).d_t.symm
  | with_reducible exact APre.stk_t' ‹APre _ _›
  | with_reducible exact (APre.stk_t' ‹APre _ _›).symm
  | with_reducible exact ret_stk _)

/-- A region is disjoint from each of a list of regions. -/
macro "rdisj_all" : tactic => `(tactic| (
  simp only [macR, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  repeat' apply And.intro
  all_goals rdisj))

theorem hRDX (s₀ : State) : s₀.gpr .rcx = BitVec.ofNat 64 (AL s₀) := by simp [AL]

theorem srcA {s₀ : State} (hp : APre e s₀) : Src s₀ (ad s₀) (AL s₀) :=
  ⟨(s₀.gpr .rcx).isLt, hp.wrap_a, hp.c_a, hp.stk_a, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.a_rd], hc⟩⟩

theorem srcD {s₀ : State} (hp : APre e s₀) : Src s₀ (dp s₀) (L s₀) :=
  ⟨(s₀.gpr .r9).isLt, hp.wrap_d, hp.c_d, hp.stk_d, fun a n ⟨r, hr, hc⟩ => ⟨r, by
    simp only [List.mem_singleton] at hr; subst hr; simp [hp.d_wr], hc⟩⟩

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The `len` bytes at `P` (in `p` and `n`), padded with zeros, and then the
lengths block at `ctx + 592`, absorbed: the padded last block with it, in
one call. -/
theorem macPadLengths_ok (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State} (hp : APre e s₀) {p n : Reg}
    (hr : MacRegs p n) {P : Addr} {len : Nat} (hs : Src s₀ P len) {s : State} (h : Inv s₀ s)
    (hP : s.gpr p = P) (hn : s.gpr n = BitVec.ofNat 64 len) :
    WP isa (macPadLengths b p n) s fun s' => Inv s₀ s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      Frame (macR s₀) s.mem s'.mem ∧ s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key
          (msg ++ (bytesAt s.mem P len ++ pad16 (bytesAt s.mem P len)) ++ bytesAt s.mem (off (cx s₀) 592) 16) := by
  have hpc : p ∈ calleeSaved := by rcases hr.1 with rfl | rfl <;> simp [calleeSaved]
  have hnc : n ∈ calleeSaved := by rcases hr.2 with rfl | rfl <;> simp [calleeSaved]
  have hcP : (ctxR s₀).Disjoint ⟨P, len⟩ := hs.ctx
  have hlt := hs.lt
  refine WP.seq (WP.mono (wholeBlocks_ok b hp hr hs h.r15 h.rsp h.rd h.wr hP hn)
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, repr₂⟩ => ?_)
  have i₂ := mac_inv hp h cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono_mx (by rcases hr with ⟨rfl | rfl, rfl | rfl⟩ <;> decide +kernel)
    (macTail_ok hr hlt (by rw [cs₂ n hnc, hn]))
    fun s₃ ⟨rdx₃, zf₃, g₃, rd₃, wr₃, m₃⟩ mx₃ => ?_)
  have cs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r h => by
    rw [g₃ r (calleeSaved_ne h).2.2.1, cs₂ r h]
  have i₃ : Inv s₀ s₃ := i₂.step (fun r h => g₃ r (calleeSaved_ne h).2.2.1) rd₃ wr₃ (rs := [])
    (by rw [m₃]; exact Frame.refl _ _) (fun _ h => by simp at h) (fun _ h => by simp at h)
  have hdisjP : ∀ r ∈ macR s₀, (⟨P, len⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hcP.sub_left (sub_ctx s₀ (by lit_omega))).symm
    · exact hs.stk.symm
  have L₂ : bytesAt s₂.mem (off (cx s₀) 592) 16 = bytesAt s.mem (off (cx s₀) 592) 16 :=
    bytesAt_frame f₂ (by rdisj_all) (by lit_omega)
  have x_eq : bytesAt s.mem P len = bytesAt s.mem P (16 * (len / 16)) ++
      bytesAt s.mem (P + BitVec.ofNat 64 (16 * (len / 16))) (len % 16) := by
    rw [← VG.Proof.Poly1305.bytesAt_add, Nat.div_add_mod]
  have hlen : (bytesAt s.mem P len).length = len := VG.Proof.Poly1305.length_bytesAt _ _ _
  refine WP.ite (decide (len % 16 = 0)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have h0 : len % 16 = 0 := by simpa using hz
    refine WP.mono (absorbLengths_ok b hp i₃) fun s₄ ⟨i₄, cs₄, f₄, mx₄, r₄⟩ => ?_
    refine ⟨i₄, fun r h => by rw [cs₄ r h, cs₃ r h], f₂.trans (by rw [← m₃]; exact f₄),
      by rw [mx₄, mx₃, mx₂], fun key msg hr => ?_⟩
    have := r₄ key _ (by rw [m₃]; exact repr₂ key msg hr)
    rw [m₃, L₂] at this
    rwa [show pad16 (bytesAt s.mem P len) = [] by simp [pad16, hlen, h0], List.append_nil,
      ← show 16 * (len / 16) = len by omega]
  · have h0 : len % 16 ≠ 0 := by simpa using hz
    refine WP.mono (macRest_ok b (k := 2) (.inr rfl) hp hr hs h0
      (by rw [cs₃ _ (by simp [calleeSaved]), h.r15])
      (by rw [cs₃ _ (by simp [calleeSaved]), h.rsp]) (by rw [rd₃, rd₂, h.rd]) (by rw [wr₃, wr₂, h.wr])
      (by rw [cs₃ p hpc, hP]) (by rw [cs₃ n hnc, hn]) rdx₃) fun s₅ ⟨cs₅, rd₅, wr₅, f₅, mx₅, repr₅⟩ => ?_
    refine ⟨mac_inv hp i₃ cs₅ rd₅ wr₅ f₅, fun r h => by rw [cs₅ r h, cs₃ r h],
      f₂.trans (by rw [← m₃]; exact f₅), by rw [mx₅, mx₃, mx₂], fun key msg hr => ?_⟩
    have := repr₅ key _ (by rw [m₃]; exact repr₂ key msg hr)
    rw [m₃, bytesAt_frame f₂ (fun r hr => (hdisjP r hr).sub_left
      (sub_off P (a := 16 * (len / 16)) (by lit_omega))) (by lit_omega), L₂] at this
    rw [show pad16 (bytesAt s.mem P len) = List.replicate (16 - len % 16) 0 by simp [pad16, hlen, h0],
      x_eq]
    simpa only [List.append_assoc, show 16 * 2 - 16 = 16 from rfl] using this

/-- The return address is unchanged. -/
theorem ret_kept {s₀ : State} (hp : APre e s₀) {m₆ m' : Mem} (hi : Frame [workR s₀, dR s₀, stkR s₀] s₀.mem m₆)
    {R : Region} (hR : (retR s₀).Disjoint R) (hf : Frame [sub s₀ 448 128, R, stkR s₀] m₆ m') :
    m'.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
  have c : (retR s₀).Contains (s₀.gpr .rsp) (64 / 8) := Region.contains_self _ _
  rw [hf.readW c (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨by rdisj, hR, by rdisj⟩) (by lit_omega), hi.readW c (by rdisj_all) (by lit_omega)]

theorem prologue_mx (v : Proof.ChaCha20.X86_64.XorImpl) :
    (prologue v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [prologue, Code.allInstrs, v.mxcsr]
  rfl

/-- The keystream in `ctx[736, 1696)` survives a frame apart from it. -/
theorem ks_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sub s₀ 672 1024).Disjoint r) {M : Nat} (hM : M ≤ 960) {f : Nat → Byte}
    (h : ∀ k < M, m (off (cx s₀) (736 + k)) = f k) : ∀ k < M, m' (off (cx s₀) (736 + k)) = f k := by
  intro k hk
  rw [← h k hk]
  exact hf _ fun r hr hc => hd r hr _ (contains_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hc

theorem crypt_mx (v : Proof.ChaCha20.X86_64.XorImpl) :
    (crypt v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [crypt, Code.allInstrs, v.mxcsr]
  rfl

theorem seal_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa («seal» v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ sealX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  refine WP.seq (WP.mono_mx (by decide +kernel) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (prologue_mx v) (prologue_ok v hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₃ (by rdisj_all), stateAt_frame f₂ (by rdisj_all), h₁.st]
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₃ (by rdisj_all) hL', bytesAt_frame f₂ (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  have hM := Nat.le_trans (mOf_le v.callee.fold (L s₀)) v.fold_le
  have ks₃ := ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks)
  refine WP.seq (WP.mono_mx (crypt_mx v) (crypt_ok v hp i₃ st₃ ks₃) fun s₄ ⟨i₄, _, f₄, ct₄⟩ mx₄ => ?_)
  rw [D₃] at ct₄
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₄
    i₄.r14 (by rw [i₄.r13]; exact hL s₀))
    fun s₆ ⟨i₆, _, f₆, mx₆, r₆⟩ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTag_ok hp i₆)
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp rdi₇ (i₆.saved.frame f₇ (by rdisj_all))
    (by rw [cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₇, i₆.rd]) (by rw [wr₇, i₆.wr])) fun s₈ ⟨cs₈, _, m₈⟩ mx₈ => ?_
  have R₄ := Repr.frame f₄ (by rdisj_all) (Repr.frame f₃ (by rdisj_all) (r₂ (otk s₀) [] h₁.poly))
  have T₇ := tag₇ _ _ (r₆ _ _ R₄)
  have L₄ : bytesAt s₄.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame f₄ (by rdisj_all) (by lit_omega), len₃]
  have C₈ : bytesAt s₈.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₈, bytesAt_frame f₇ (by rdisj_all) hL', bytesAt_frame f₆ (by rdisj_all) hL', ct₄]
  have C₄ : bytesAt s₄.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := ct₄
  refine ⟨⟨cs₈, by rw [m₈]; exact ret_kept hp i₆.frame hp.ret_t f₇,
    by rw [mx₈, mx₇, mx₆, mx₄, mx₃, mx₂, mx₁, mx₀]⟩, ?_⟩
  show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
    (bytesAt s₈.mem (dp s₀) (L s₀), bytesAt s₈.mem (tp s₀) 16)
  rw [C₈, m₈, T₇, L₄, C₄, hA]
  simp only [Spec.ChaCha20Poly1305.encrypt, macData, List.nil_append,
    List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]

theorem open_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa («open» v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  have hL' := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  refine WP.seq (WP.mono_mx (by decide +kernel) (entry_ok hp) fun s₀' e₀ mx₀ => ?_)
  subst e₀
  refine WP.seq (WP.mono_mx (prologue_mx v) (prologue_ok v hp) fun s₁ h₁ mx₁ => ?_)
  have hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.fine (by rdisj_all) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
  refine WP.seq (WP.mono (macPad_ok v.poly hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp)
    h₁.inv.r15 h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, mx₂, r₂⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  have D₂ : bytesAt s₂.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame f₂ (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  refine WP.seq (WP.mono_mx (by decide +kernel) (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]),
    h₁.rbp])) fun s₃ ⟨i₃, _, f₃, len₃⟩ mx₃ => ?_)
  have D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by rw [bytesAt_frame f₃ (by rdisj_all) hL', D₂]
  refine WP.seq (WP.mono (macPadLengths_ok v.poly hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₃
    i₃.r14 (by rw [i₃.r13]; exact hL s₀)) fun s₅ ⟨i₅, _, f₅, mx₅, r₅⟩ => ?_)
  have st₅ : stateAt s₅.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame f₅ (by rdisj_all), stateAt_frame f₃ (by rdisj_all),
      stateAt_frame f₂ (by rdisj_all), h₁.st]
  have hM := Nat.le_trans (mOf_le v.callee.fold (L s₀)) v.fold_le
  have ks₅ := ks_frame f₅ (by rdisj_all) hM (ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks))
  refine WP.seq (WP.mono_mx (crypt_mx v) (crypt_ok v hp i₅ st₅ ks₅) fun s₆ ⟨i₆, _, f₆, pt₆⟩ mx₆ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (finalizeTo_ok hp i₆ (out := 48) (.inl (by omega)))
    fun s₇ ⟨cs₇, rd₇, wr₇, rdi₇, rcx₇, f₇, tag₇⟩ mx₇ => ?_)
  refine WP.block_append (WP.mono_mx (by decide +kernel) (compare_ok hp rcx₇
    (by rw [cs₇ _ (by simp [calleeSaved]), i₆.r12]) (by rw [rd₇, i₆.rd])
    (by rw [wr₇, i₆.wr])) fun s₈ ⟨rax₈, g₈, m₈, rd₈, wr₈⟩ mx₈ => ?_)
  refine WP.mono_mx (by decide +kernel) (restore_ok hp (by rw [g₈ _ (by decide) (by decide), rdi₇])
    (by rw [m₈]; exact i₆.saved.frame f₇ (by rdisj_all))
    (by rw [g₈ _ (by decide) (by decide), cs₇ _ calleeSaved_rsp, i₆.rsp])
    (by rw [rd₈, rd₇, i₆.rd]) (by rw [wr₈, wr₇, i₆.wr])) fun s₉ ⟨cs₉, rax₉, m₉⟩ mx₉ => ?_
  -- The tag computed, and the one received.
  have R₂ := r₂ (otk s₀) [] h₁.poly
  have T₇ := tag₇ _ _ (Repr.frame f₆ (by rdisj_all) (r₅ _ _ (Repr.frame f₃ (by rdisj_all) R₂)))
  have L₃ : bytesAt s₃.mem (off (cx s₀) 592) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := len₃
  have T0₇ : bytesAt s₇.mem (tp s₀) 16 = T0 s₀ := by
    rw [bytesAt_frame f₇ (by rdisj_all) (by lit_omega), bytesAt_frame i₆.frame (by rdisj_all) (by lit_omega)]
  have P₉ : bytesAt s₉.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
    rw [m₉, m₈, bytesAt_frame f₇ (by rdisj_all) hL', pt₆, bytesAt_frame f₅ (by rdisj_all) hL', D₃]
  rw [L₃, D₃, hA] at T₇
  refine ⟨⟨cs₉, by rw [m₉, m₈]; exact ret_kept hp i₆.frame (hp.ret_c.sub_right (sub_ctx _ (by lit_omega))) f₇,
    by rw [mx₉, mx₈, mx₇, mx₆, mx₅, mx₃, mx₂, mx₁, mx₀]⟩, ?_⟩
  have hm : mac (otk s₀) (macData (A s₀) (D s₀)) = bytesAt s₇.mem (off (cx s₀) 48) 16 := by
    rw [T₇]
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt]
  rw [openX86_64, Contract.post_mk]
  rw [rax₉, rax₈]
  split
  next pt hpt =>
    obtain ⟨hmac, rfl⟩ := decrypt_eq_some hpt
    exact ⟨ite_eq_left (hm.symm.trans (hmac.trans T0₇.symm)), P₉⟩
  next hn => exact ite_eq_right fun he => decrypt_eq_none hn ((hm.trans he).trans T0₇)

end VG.Proof.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: constant time

`seal` and `open` load `work` and `tag` from the stack first (`entry`), which
the taint analysis cannot follow, as it knows nothing of the stack arguments:
both runs load the same pointers, which the public data includes, and leak
the same addresses (`entry_rel`). They call an implementation of
`vg_chacha20_xor` that the proof does not know, so the taint analysis cannot
follow them into it either. The code from the entry to the call and the code
after it are checked by the taint analysis; the call is constant time by the
implementation's own proof (`RelCT.callEx`), since its arguments, which
correctness determines (`XArgs`), agree in two runs; and after it,
correctness says again where `rsi` points (`After`), from which the rest is
checked.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64

variable {e : Bool}

/-- The index of the working space among the writable regions:
`[data, tag, work]` for `seal`, `[data, work]` for `open`. -/
abbrev ci (enc : Bool) : Nat := bif enc then 2 else 1

/-- What the analysis knows of the lengths of the writable regions: the
data's varies. -/
abbrev lensOf (enc : Bool) : List Nat := bif enc then [0, 16, 1696] else [0, 1696]

/-- The public registers and what is known about memory after the entry: the
lengths of the regions and the registers holding the bases of the working
space (`rax`) and the data. -/
def τ₀ (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp, .rax, .r11], flags := false,
    lens := lensOf enc, bases := [(.rax, ci enc, 0), (.r8, 0, 0)] }

/-- The writable regions on entry. -/
theorem APre.wr_eq {s₀ : State} (hp : APre e s₀) :
    s₀.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by
  rw [hp.wr]; cases e <;> rfl

theorem pub_regs {s₁ s₂ : State} (hq : pubX86_64 s₁ s₂) :
    ctxR s₁ = ctxR s₂ ∧ dR s₁ = dR s₂ ∧ tR s₁ = tR s₂ := by
  obtain ⟨-, -, -, -, p5, p6, -, p8, p9⟩ := hq
  simp only [ctxR, dR, tR, cx, dp, L, tp, p5, p6, p8, p9, and_self]

theorem wf₀ {s₀ : State} (hp : APre e s₀) : X86_64.Taint.Wf (τ₀ e) (entryS s₀) := by
  have hl := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  have hw := hp.wr_eq
  have g : ∀ r, (entryS s₀).gpr r = if r = .r11 then tp s₀ else if r = .rax then cx s₀ else s₀.gpr r := by
    intro r; simp [entryS, State.setReg]
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hm => ?_⟩
  · show List.Forall₂ _ s₀.wr _
    rw [hw]; cases e <;> simp [τ₀]
  · show s₀.wr.Pairwise _
    rw [hw]
    cases e <;> simp [hp.d_t, hp.c_d.symm, hp.c_t.symm]
  · show ∀ r ∈ s₀.wr, _
    rw [hw]; cases e <;> simp [hl]
  · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;>
      simp [X86_64.Taint.region, show (entryS s₀).wr = s₀.wr from rfl, hw, g] <;> cases e <;> simp

theorem agree₀ {s₁ s₂ : State} (h₁ : APre e s₁) (h₂ : APre e s₂) (hq : pubX86_64 s₁ s₂) :
    X86_64.Taint.Agree (τ₀ e) (entryS s₁) (entryS s₂) := by
  have hq' := hq
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hq'
  obtain ⟨c, d, t⟩ := pub_regs hq
  have g : ∀ s r, (entryS s).gpr r = if r = .r11 then tp s else if r = .rax then cx s else s.gpr r := by
    intro s r; simp [entryS, State.setReg]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g, g]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, ↓reduceIte] <;> with_reducible assumption
  · show s₁.wr = s₂.wr
    rw [h₁.wr_eq, h₂.wr_eq, c, d, t]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-! ## The entry -/

theorem entry_rel {s₀ s₀' : State} (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry)
      fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀' := by
  rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  cases e₁ with | block h₁ => cases e₂ with | block h₂ =>
  rw [entry_run hp] at h₁
  rw [entry_run hp'] at h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
  obtain ⟨rfl, rfl⟩ := h₁
  obtain ⟨rfl, rfl⟩ := h₂
  exact ⟨by rw [hq.2.2.2.2.2.2.1], rfl, rfl⟩

/-! ## The parts of the code -/

/-- From the call of `vg_chacha20_xor` in the prologue to the branch on the
length: `seal`'s. -/
def sealMid (fold : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq prologueB (.seq (macPad b .rbx .rbp) (.seq (.block lengths)
    (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (fold + 1)))])))

/-- `open`'s. -/
def openMid (fold : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq prologueB (.seq (macPad b .rbx .rbp) (.seq (.block lengths) (.seq (macPadLengths b .r14 .r13)
    (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (fold + 1)))]))))

/-- The branch for at most `fold` bytes. -/
def cryptSmall : Prog isa :=
  .seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
    (.seq (xorBufX .r14) (.block (ptr .rsi .r15 128)))

/-- The branch on the length. -/
def cryptIte (x : Impl.ChaCha20.X86_64.Callee) : Prog isa :=
  .ite .b cryptSmall (.seq (.block cryptArgs) (.call x.name x.code))

/-- The keystream wiped. -/
def wipe (fold : Nat) : Prog isa :=
  .seq (.block (anchor .rsi 128)) (.seq (foldM fold) (.seq (.block [.alu .add .rdx (.imm 64)]) zeroKs))

/-- `seal` after the branch. -/
def sealPost (fold : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (wipe fold) (.seq (macPadLengths b .r14 .r13) (.seq finalizeTag (.block restore)))

/-- `open` after the branch. -/
def openPost (fold : Nat) : Prog isa :=
  .seq (wipe fold) (.seq (finalizeTo 48) (.block (compare ++ restore)))

theorem seal_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa («seal» x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold) (.seq (.call x.name x.code)
      (.seq (sealMid x.fold b) (.seq (cryptIte x) (sealPost x.fold b)))))) s t s' := by
  cases h with | seq e₀ h => cases h with | seq hP h => cases hP with | seq ePA hP => cases hP with
  | seq eC ePB => cases h with | seq eMA h => cases h with | seq eLEN h => cases h with | seq hC h =>
  cases hC with | seq eCMP hC => cases hC with | seq eITE hC => cases hC with | seq eANC hC =>
  cases hC with | seq eFM hC => cases hC with | seq eADD eZK => cases h with | seq eMC h =>
  cases h with | seq eFT eRE =>
  have := Exec.seq e₀ (Exec.seq ePA (Exec.seq eC (Exec.seq (Exec.seq ePB (Exec.seq eMA (Exec.seq eLEN eCMP)))
    (Exec.seq eITE (Exec.seq (Exec.seq eANC (Exec.seq eFM (Exec.seq eADD eZK)))
      (Exec.seq eMC (Exec.seq eFT eRE)))))))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem open_exec {x : Impl.ChaCha20.X86_64.Callee} {b : Impl.Poly1305.X86_64.Blocks} {s s' : State}
    {t : List Leak} (h : Exec isa («open» x b) s t s') :
    Exec isa (.seq (.block entry) (.seq (prologueA x.fold) (.seq (.call x.name x.code)
      (.seq (openMid x.fold b) (.seq (cryptIte x) (openPost x.fold)))))) s t s' := by
  cases h with | seq e₀ h => cases h with | seq hP h => cases hP with | seq ePA hP => cases hP with
  | seq eC ePB => cases h with | seq eMA h => cases h with | seq eLEN h => cases h with | seq eMC h =>
  cases h with | seq hC h =>
  cases hC with | seq eCMP hC => cases hC with | seq eITE hC => cases hC with | seq eANC hC =>
  cases hC with | seq eFM hC => cases hC with | seq eADD eZK => cases h with | seq eFIN eCR =>
  have := Exec.seq e₀ (Exec.seq ePA (Exec.seq eC (Exec.seq
    (Exec.seq ePB (Exec.seq eMA (Exec.seq eLEN (Exec.seq eMC eCMP))))
    (Exec.seq eITE (Exec.seq (Exec.seq eANC (Exec.seq eFM (Exec.seq eADD eZK))) (Exec.seq eFIN eCR))))))
  simp only [List.append_assoc] at this ⊢
  exact this

theorem RelCT.of_exec {P Q : State → State → Prop} {c c' : Prog isa}
    (he : ∀ {s t s'}, Exec isa c s t s' → Exec isa c' s t s') (h : RelCT isa P c' Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (he e₁) (he e₂)

/-- At the branch on the length. -/
structure AtIte (fold : Nat) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  cf : s.cf = some (decide (L s₀ < fold + 1))
  ks : ∀ k < mOf fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
    (Spec.ChaCha20.keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0

theorem cmpIte_ok {fold : Nat} (hf : fold ≤ 960) {s₀ : State} {s : State} (h : Inv s₀ s)
    (hks : ∀ k < mOf fold (L s₀), s.mem (off (cx s₀) (736 + k)) =
      (Spec.ChaCha20.keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)).getD k 0) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (fold + 1)))]) s (AtIte fold s₀) :=
  WP.mono (cmpFold_ok (by lit_omega) h.r13) fun _ ⟨g₁, rd₁, wr₁, m₁, c₁⟩ =>
    ⟨h.step (fun r _ => by rw [g₁]) rd₁ wr₁ (rs := []) (by rw [m₁]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h), c₁, by rw [m₁]; exact hks⟩

theorem sealMid_ok {fold : Nat} (hf : fold ≤ 960) (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AfterF fold s₀ s) : WP isa (sealMid fold b) s (AtIte fold s₀) := by
  have hM := Nat.le_trans (mOf_le fold (L s₀)) hf
  refine WP.seq (WP.mono (prologueB_ok hf hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, _⟩ => ?_)
  exact cmpIte_ok hf i₃ (ks_frame f₃ (by rdisj_all) hM (ks_frame f₂ (by rdisj_all) hM h₁.ks))

theorem openMid_ok {fold : Nat} (hf : fold ≤ 960) (b : Impl.Poly1305.X86_64.Blocks) {s₀ : State}
    (hp : APre e s₀) {s : State} (h : AfterF fold s₀ s) : WP isa (openMid fold b) s (AtIte fold s₀) := by
  have hM := Nat.le_trans (mOf_le fold (L s₀)) hf
  refine WP.seq (WP.mono (prologueB_ok hf hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (macPad_ok b hp (p := .rbx) (n := .rbp) ⟨.inl rfl, .inl rfl⟩ (srcA hp) h₁.inv.r15
    h₁.inv.rsp h₁.inv.rd h₁.inv.wr h₁.rbx (by rw [h₁.rbp]; exact hRDX s₀))
    fun s₂ ⟨cs₂, rd₂, wr₂, f₂, _⟩ => ?_)
  have i₂ := mac_inv hp h₁.inv cs₂ rd₂ wr₂ f₂
  refine WP.seq (WP.mono (lengths_ok hp i₂ (by rw [cs₂ _ (by simp [calleeSaved]), h₁.rbp]))
    fun s₃ ⟨i₃, _, f₃, _⟩ => ?_)
  refine WP.seq (WP.mono (macPadLengths_ok b hp (p := .r14) (n := .r13) ⟨.inr rfl, .inr rfl⟩ (srcD hp) i₃
    i₃.r14 (by rw [i₃.r13]; exact hL s₀)) fun s₄ ⟨i₄, _, f₄, _⟩ => ?_)
  exact cmpIte_ok hf i₄ (ks_frame f₄ (by rdisj_all) hM (ks_frame f₃ (by rdisj_all) hM
    (ks_frame f₂ (by rdisj_all) hM h₁.ks)))

/-! ## After the call -/

/-- What is known after the call of `vg_chacha20_xor`, in one run. -/
structure After (s₀ s : State) : Prop where
  rsi : s.gpr .rsi = off (cx s₀) 128
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r13 : s.gpr .r13 = s₀.gpr .r9
  r14 : s.gpr .r14 = dp s₀
  r12 : s.gpr .r12 = tp s₀
  wr : s.wr = s₀.wr

/-- The taint after the call: `rsi` points at `ctx + 128`, and the lengths of
the regions are those on entry. -/
def τ₁ (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.rsi, .rsp, .r13, .r14, .r12], flags := false, lens := lensOf enc,
    bases := [(.rsi, ci enc, 128)] }

section
variable {s₀ s₀' : State} (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀')

omit hp' in
include hp in
theorem After.wf {s : State} (h : After s₀ s) : X86_64.Taint.Wf (τ₁ e) s := by
  have hl := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  have hw : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [h.wr, hp.wr_eq]
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hm => ?_⟩
  · rw [hw]; cases e <;> simp [τ₁]
  · rw [hw]; cases e <;> simp [hp.d_t, hp.c_d.symm, hp.c_t.symm]
  · rw [hw]; cases e <;> simp [hl]
  · simp only [τ₁, List.mem_singleton] at hm
    subst hm
    simp only [X86_64.Taint.region, hw, h.rsi, off_eq]
    cases e <;> simp

include hp hp' hq in
theorem agree₁ {s₁ s₂ : State} (h₁ : After s₀ s₁) (h₂ : After s₀' s₂) : X86_64.Taint.Agree (τ₁ e) s₁ s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, p8, p9⟩ := hq'
  obtain ⟨c, d, t⟩ := pub_regs hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τ₁, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.rsi, h₂.rsi, cx, cx, p9]
    · rw [h₁.rsp, h₂.rsp, p7]
    · rw [h₁.r13, h₂.r13, p6]
    · rw [h₁.r14, h₂.r14, dp, dp, p5]
    · rw [h₁.r12, h₂.r12, tp, tp, p8]
  · rw [h₁.wr, h₂.wr, hp.wr_eq, hp'.wr_eq, c, d, t]
  · intro sl h; simp [τ₁] at h
  · intro sl h; simp [τ₁] at h

include hp hp' hq in
/-- The call of any implementation `v` of `vg_chacha20_xor`. -/
theorem call_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun s₁ s₂ => XArgs s₀ s₁ ∧ XArgs s₀' s₂) (.call v.callee.name v.callee.code)
      fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq
  have ct := RelCT.callEx (n := v.callee.name) (P := fun s₁ s₂ => XArgs s₀ s₁ ∧ XArgs s₀' s₂) v.ok v.ct fun s₁ s₂ ⟨a₁, a₂⟩ =>
    ⟨[], _, [], _, a₁.pre hp v, a₂.pre hp' v, by
      simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.rsp, a₂.rdi,
        a₂.rsi, a₂.rdx, a₂.rcx, a₂.rsp, cx, dp, p5, p6, p7, p9]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩,
      (Covers.right (a₁.hw hp)), a₁.hw hp, (Covers.right (a₂.hw hp')),
      a₂.hw hp', by rw [a₁.rsp, a₂.rsp, p7]⟩
  have after : ∀ {σ₀ s : State}, APre e σ₀ → XArgs σ₀ s →
      WP isa (.call v.callee.name v.callee.code) s (After σ₀) := fun hp a =>
    a.call hp v fun _ _ wr cs _ rsi _ =>
      ⟨rsi, by rw [cs _ calleeSaved_rsp, a.rsp], by rw [cs _ (by simp [calleeSaved]), a.r13],
        by rw [cs _ (by simp [calleeSaved]), a.r14], by rw [cs _ (by simp [calleeSaved]), a.r12],
        by rw [wr, a.wr]⟩
  exact (ct.wp fun _ _ h => ⟨after hp h.1, after hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end

/-! ## The call in the prologue, and the branch -/

/-- The taint after the call in the prologue: as `τ₁`, and `rbx` and `rbp`
(the additional data and its length) are public. -/
def τA (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.rsi, .rsp, .r13, .r14, .r12, .rbx, .rbp], flags := false, lens := lensOf enc,
    bases := [(.rsi, ci enc, 128)] }

/-- The taint at the branch: the context's address and the data's are public. -/
def τS (enc : Bool) : X86_64.Taint.T :=
  { regs := .ofList [.r15, .rsp, .r13, .r14, .r12], flags := false, lens := lensOf enc,
    bases := [(.r15, ci enc, 0), (.r14, 0, 0)] }

section
variable {s₀ s₀' : State} (hp : APre e s₀) (hp' : APre e s₀') (hq : pubX86_64 s₀ s₀')

omit hp' in
include hp in
theorem regions_wf {s : State} (hw : s.wr = s₀.wr) :
    List.Forall₂ (fun r l => l ≤ r.len) s.wr (lensOf e) ∧ s.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s.wr, r.len ≤ 2 ^ 64 := by
  have hl := (Nat.le_of_lt (s₀.gpr .r9).isLt)
  have hw' : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [hw, hp.wr_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw']; cases e <;> simp
  · rw [hw']; cases e <;> simp [hp.d_t, hp.c_d.symm, hp.c_t.symm]
  · rw [hw']; cases e <;> simp [hl]

include hp in
omit hp' in
theorem AfterF.wf {fold : Nat} {s : State} (h : AfterF fold s₀ s) : X86_64.Taint.Wf (τA e) s := by
  have hw : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [h.wr, hp.wr_eq]
  refine ⟨fun _ => regions_wf hp h.wr, fun p hm => ?_⟩
  simp only [τA, List.mem_singleton] at hm
  subst hm
  simp only [X86_64.Taint.region, hw, h.rsi, off_eq]
  cases e <;> simp

include hp hp' hq in
theorem agreeA {fold : Nat} {s₁ s₂ : State} (h₁ : AfterF fold s₀ s₁) (h₂ : AfterF fold s₀' s₂) :
    X86_64.Taint.Agree (τA e) s₁ s₂ := by
  have hq' := hq
  obtain ⟨-, -, p3, p4, p5, p6, p7, p8, p9⟩ := hq'
  obtain ⟨c, d, t⟩ := pub_regs hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.rsi, h₂.rsi, cx, cx, p9]
    · rw [h₁.rsp, h₂.rsp, p7]
    · rw [h₁.r13, h₂.r13, p6]
    · rw [h₁.r14, h₂.r14, dp, dp, p5]
    · rw [h₁.r12, h₂.r12, tp, tp, p8]
    · rw [h₁.rbx, h₂.rbx, ad, ad, p3]
    · rw [h₁.rbp, h₂.rbp, p4]
  · rw [h₁.wr, h₂.wr, hp.wr_eq, hp'.wr_eq, c, d, t]
  · intro sl h; simp [τA] at h
  · intro sl h; simp [τA] at h

include hp in
omit hp' in
theorem AtIte.wf {fold : Nat} {s : State} (h : AtIte fold s₀ s) : X86_64.Taint.Wf (τS e) s := by
  have hw : s.wr = bif e then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀] := by rw [h.inv.wr, hp.wr_eq]
  refine ⟨fun _ => regions_wf hp h.inv.wr, fun p hm => ?_⟩
  simp only [τS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;>
    simp only [X86_64.Taint.region, hw, h.inv.r15, h.inv.r14] <;> cases e <;> simp

include hp hp' hq in
theorem agreeS {fold : Nat} {s₁ s₂ : State} (h₁ : AtIte fold s₀ s₁) (h₂ : AtIte fold s₀' s₂) :
    X86_64.Taint.Agree (τS e) s₁ s₂ := by
  have hq' := hq
  obtain ⟨-, -, -, -, p5, p6, p7, p8, p9⟩ := hq'
  obtain ⟨c, d, t⟩ := pub_regs hq
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, h₁.wf hp, h₂.wf hp', ?_, ?_, X86_64.Taint.noLo⟩
  · simp only [τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h₁.inv.r15, h₂.inv.r15, cx, cx, p9]
    · rw [h₁.inv.rsp, h₂.inv.rsp, p7]
    · rw [h₁.inv.r13, h₂.inv.r13, p6]
    · rw [h₁.inv.r14, h₂.inv.r14, dp, dp, p5]
    · rw [h₁.inv.r12, h₂.inv.r12, tp, tp, p8]
  · rw [h₁.inv.wr, h₂.inv.wr, hp.wr_eq, hp'.wr_eq, c, d, t]
  · intro sl h; simp [τS] at h
  · intro sl h; simp [τS] at h

omit hp' hq in
include hp in
theorem FArgs.hw {fold : Nat} (hf : fold ≤ 960) {s : State} (h : FArgs fold s₀ s) :
    Covers [⟨off (cx s₀) 608, 64⟩, ⟨off (cx s₀) 672, 64 + mOf fold (L s₀)⟩, ⟨off (cx s₀) 128, 320⟩] s.wr := by
  have hm := mOf_le fold (L s₀)
  refine covers_sub hp h.wr _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨608, rfl, show 608 + 64 ≤ 1696 by omega⟩
  · exact ⟨672, rfl, show 672 + (64 + mOf fold (L s₀)) ≤ 1696 by omega⟩
  · exact ⟨128, rfl, show 128 + 320 ≤ 1696 by omega⟩

omit hp' hq in
include hp in
theorem FArgs.pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} (h : FArgs v.callee.fold s₀ s) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions []
      [⟨off (cx s₀) 608, 64⟩, ⟨off (cx s₀) 672, 64 + mOf v.callee.fold (L s₀)⟩, ⟨off (cx s₀) 128, 320⟩]) := by
  have hm := mOf_le v.callee.fold (L s₀)
  have hfl := v.fold_le
  exact xor_pre v h.rdi h.rsi h.rdx h.rcx (by lit_omega)
    (sub_disj s₀ (b := 672) (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
    (sub_disj s₀ (a := 672) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega)) (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))
    (by rw [h.rsp]; exact hp.stk_sub (by lit_omega))

include hp hp' hq in
/-- The call in the prologue, of any implementation `v` of `vg_chacha20_xor`. -/
theorem call1_rel (v : Proof.ChaCha20.X86_64.XorImpl) :
    RelCT isa (fun s₁ s₂ => FArgs v.callee.fold s₀ s₁ ∧ FArgs v.callee.fold s₀' s₂)
      (.call v.callee.name v.callee.code)
      fun s₁ s₂ => AfterF v.callee.fold s₀ s₁ ∧ AfterF v.callee.fold s₀' s₂ := by
  obtain ⟨-, -, -, -, p5, p6, p7, -, p9⟩ := hq
  have hfl := v.fold_le
  have ct := RelCT.callEx (n := v.callee.name)
    (P := fun s₁ s₂ => FArgs v.callee.fold s₀ s₁ ∧ FArgs v.callee.fold s₀' s₂) v.ok v.ct fun s₁ s₂ ⟨a₁, a₂⟩ =>
    ⟨[], _, [], _, a₁.pre hp v, a₂.pre hp' v, by
      simp only [Proof.ChaCha20.xorStack, Proof.ChaCha20.xorX86_64, State.withRegions_gpr,
        State.callEntry_rsp, callEntry_gpr' s₁ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₁ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₁ (by decide : Reg.rcx ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s₂ (by decide : Reg.rdx ≠ .rsp),
        callEntry_gpr' s₂ (by decide : Reg.rcx ≠ .rsp), a₁.rdi, a₁.rsi, a₁.rdx, a₁.rcx, a₁.rsp, a₂.rdi,
        a₂.rsi, a₂.rdx, a₂.rcx, a₂.rsp, cx, L, p6, p7, p9]
      exact ⟨trivial, trivial, trivial, trivial, trivial⟩,
      (Covers.right (a₁.hw hp hfl)), a₁.hw hp hfl, (Covers.right (a₂.hw hp' hfl)),
      a₂.hw hp' hfl, by rw [a₁.rsp, a₂.rsp, p7]⟩
  exact (ct.wp fun _ _ h => ⟨foldCall_ok v hp h.1, foldCall_ok v hp' h.2⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

omit hp' hq in
include hp in
theorem small_ok {fold : Nat} (hf : fold ≤ 960) {s : State} (h : AtIte fold s₀ s) (hle : L s₀ ≤ fold) :
    WP isa cryptSmall s (After s₀) :=
  WP.mono (cryptSmall_ok hf hp h.inv hle h.ks) fun _ c =>
    ⟨c.rsi, by rw [c.cs _ calleeSaved_rsp (by decide), h.inv.rsp],
      by rw [c.cs _ (by simp [calleeSaved]) (by decide), h.inv.r13],
      by rw [c.cs _ (by simp [calleeSaved]) (by decide), h.inv.r14],
      by rw [c.cs _ (by simp [calleeSaved]) (by decide), h.inv.r12], by rw [c.wr, h.inv.wr]⟩

end

/-! ## `seal` and `open` -/

/-! The analyses of the code that the checks below share, as summaries
(`taint_summary`): the calls of the Poly1305 functions, from the registers
public at them (the larger set where the code after the call needs `rbx` and
`rbp`), for `seal` and for `open`, whose regions differ. -/

/-- The public registers at the calls of `vg_poly1305_blocks`. -/
def τB (enc big : Bool) : X86_64.Taint.T :=
  { regs := .ofList ((if big then [.rbx, .rbp] else []) ++ [.rdx, .rsp, .rsi, .rdi, .r12, .r13, .r14, .r15]),
    flags := false, lens := lensOf enc, bases := [(.rdi, ci enc, 448)] }

section
open Impl.Poly1305.X86_64.Blocks
taint_summary blocksBigS : taintS (τB true true) (.call scalar.name scalar.code)
taint_summary blocksSmallS : taintS (τB true false) (.call scalar.name scalar.code)
taint_summary blocksBigAvx2S : taintS (τB true true) (.call avx2.name avx2.code)
taint_summary blocksSmallAvx2S : taintS (τB true false) (.call avx2.name avx2.code)
taint_summary blocksBigAvx512S : taintS (τB true true) (.call avx512.name avx512.code)
taint_summary blocksSmallAvx512S : taintS (τB true false) (.call avx512.name avx512.code)
taint_summary blocksBigO : taintS (τB false true) (.call scalar.name scalar.code)
taint_summary blocksSmallO : taintS (τB false false) (.call scalar.name scalar.code)
taint_summary blocksBigAvx2O : taintS (τB false true) (.call avx2.name avx2.code)
taint_summary blocksSmallAvx2O : taintS (τB false false) (.call avx2.name avx2.code)
taint_summary blocksBigAvx512O : taintS (τB false true) (.call avx512.name avx512.code)
taint_summary blocksSmallAvx512O : taintS (τB false false) (.call avx512.name avx512.code)
end

taint_summary finalizeSumS : taintS (τB true false)
  (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.X86_64.finalize)
/-- The public registers at `open`'s call of `vg_poly1305_finalize_scratch`,
which writes the tag to `ctx + 48`, a known place in the working space, so
that `r12` (the received tag), which it saves and restores, stays public. -/
def τF : X86_64.Taint.T :=
  { regs := .ofList [.rdx, .rsp, .rsi, .rdi, .r12, .r13, .r14, .r15], flags := false,
    lens := lensOf false, bases := [(.rdi, 1, 448), (.rdx, 1, 48)] }

taint_summary finalizeSumO : taintS τF
  (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.X86_64.finalize)

/-- The pairs of `fold` and implementation of `vg_poly1305_blocks` the checks
below cover (`XorImpl.fold_poly`). -/
abbrev FoldPoly (fold : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prop :=
  (fold = 0 ∧ b = .scalar) ∨ (fold = 192 ∧ b = .avx2) ∨ (fold = 960 ∧ b = .avx512)

theorem prologueA_taint (enc : Bool) {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τ₀ enc) (prologueA fold) h).isSome = true := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> cases enc <;> taint_decide_sum []

theorem cryptSmall_taint (enc : Bool) : ∃ h, (taintS.check (τS enc) cryptSmall h).isSome = true := by
  cases enc <;> taint_decide_sum []

theorem cryptArgs_taint (enc : Bool) : ∃ h, (taintS.check (τS enc) (.block cryptArgs) h).isSome = true := by
  cases enc <;> taint_decide_sum []

theorem sealMid_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τA true) (sealMid fold b) h).isSome = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    taint_decide_sum [blocksBigS, blocksBigAvx2S, blocksBigAvx512S]

theorem sealPost_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τ₁ true) (sealPost fold b) h).isSome = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    taint_decide_sum [blocksSmallS, blocksSmallAvx2S, blocksSmallAvx512S, finalizeSumS]

theorem openMid_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τA false) (openMid fold b) h).isSome = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    taint_decide_sum [blocksBigO, blocksSmallO, blocksBigAvx2O, blocksSmallAvx2O, blocksBigAvx512O,
      blocksSmallAvx512O]

theorem openPost_taint {fold : Nat} {b : Impl.Poly1305.X86_64.Blocks} (h : FoldPoly fold b) :
    ∃ h, (taintS.check (τ₁ false) (openPost fold) h).isSome = true := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> taint_decide_sum [finalizeSumO]

section
variable (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State}

/-- The code from the entry to the end of the branch on the length, the same
for `seal` and `open` but for the code between the calls (`mid`). -/
theorem toPost_rel {enc : Bool} (hp : APre enc s₀) (hp' : APre enc s₀') (hq : pubX86_64 s₀ s₀')
    {mid : Prog isa} (hmid : RelCT isa (fun s₁ s₂ => AfterF v.callee.fold s₀ s₁ ∧ AfterF v.callee.fold s₀' s₂) mid
      (fun s₁ s₂ => AtIte v.callee.fold s₀ s₁ ∧ AtIte v.callee.fold s₀' s₂)) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block entry) (.seq (prologueA v.callee.fold) (.seq (.call v.callee.name v.callee.code)
        (.seq mid (cryptIte v.callee)))))
      fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂ := by
  have hfl := v.fold_le
  obtain ⟨_, hA⟩ := prologueA_taint enc v.fold_poly
  have pA := ((RelCT.taint (A := taintS) (P := fun s₁ s₂ => s₁ = entryS s₀ ∧ s₂ = entryS s₀') (τ₀ enc)
    (fun _ _ h => by rw [h.1, h.2]; exact agree₀ hp hp' hq) hA).wp
    (F₁ := FArgs v.callee.fold s₀) (F₂ := FArgs v.callee.fold s₀') fun _ _ h =>
    ⟨by rw [h.1]; exact prologueA_ok hfl hp, by rw [h.2]; exact prologueA_ok hfl hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have hc : ∀ s₁ s₂, (AtIte v.callee.fold s₀ s₁ ∧ AtIte v.callee.fold s₀' s₂) →
      isa.eval .b s₁ = isa.eval .b s₂ := fun s₁ s₂ h => by
    have : L s₀ = L s₀' := by simp only [L, hq.2.2.2.2.2.1]
    simp [eval, h.1.cf, h.2.cf, this]
  obtain ⟨_, hS⟩ := cryptSmall_taint enc
  obtain ⟨_, hX⟩ := cryptArgs_taint enc
  have small := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIte v.callee.fold s₀ s₁ ∧ AtIte v.callee.fold s₀' s₂) ∧ isa.eval .b s₁ = some true)
    (τS enc) (fun _ _ h => agreeS hp hp' hq h.1.1 h.1.2) hS).wp (F₁ := After s₀) (F₂ := After s₀')
    fun s₁ s₂ h => by
      have e₁ := h.2
      have e₂ := (hc _ _ h.1).symm.trans h.2
      simp only [eval, h.1.1.cf, h.1.2.cf, Option.some.injEq, decide_eq_true_eq] at e₁ e₂
      exact ⟨small_ok hp hfl h.1.1 (by omega), small_ok hp' hfl h.1.2 (by omega)⟩
  have args := (RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => (AtIte v.callee.fold s₀ s₁ ∧ AtIte v.callee.fold s₀' s₂) ∧ isa.eval .b s₁ = some false)
    (τS enc) (fun _ _ h => agreeS hp hp' hq h.1.1 h.1.2) hX).wp (F₁ := XArgs s₀) (F₂ := XArgs s₀')
    fun s₁ s₂ h => ⟨cryptArgs_ok hp h.1.1.inv, cryptArgs_ok hp' h.1.2.inv⟩
  have ite := RelCT.ite hc (small.mono (fun _ _ h => h) fun _ _ h => h.2)
    ((args.mono (fun _ _ h => h) fun _ _ h => h.2).seq (call_rel hp hp' hq v))
  exact (entry_rel hp hp' hq).seq (pA.seq ((call1_rel hp hp' hq v).seq (hmid.seq ite)))

theorem seal_rel (h₀ : preX86_64 true s₀) (h₀' : preX86_64 true s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have hfl := v.fold_le
  obtain ⟨_, hmid⟩ := sealMid_taint v.fold_poly
  obtain ⟨_, hpost⟩ := sealPost_taint v.fold_poly
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF v.callee.fold s₀ s₁ ∧ AfterF v.callee.fold s₀' s₂) (τA true)
    (fun _ _ h => agreeA hp hp' hq h.1 h.2) hmid).wp (F₁ := AtIte v.callee.fold s₀)
    (F₂ := AtIte v.callee.fold s₀') fun _ _ h =>
      ⟨sealMid_ok hfl v.poly hp h.1, sealMid_ok hfl v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τ₁ true)
    (fun _ _ h => agree₁ hp hp' hq h.1 h.2) hpost
  have := (toPost_rel v hp hp' hq mid).seq post
  refine RelCT.of_exec seal_exec ?_
  exact RelCT.of_exec (fun e => by
    cases e with | seq e₀ e => cases e with | seq eA e => cases e with | seq eC e => cases e with
    | seq eM e => cases e with | seq eI eP =>
    have := Exec.seq (Exec.seq e₀ (Exec.seq eA (Exec.seq eC (Exec.seq eM eI)))) eP
    simp only [List.append_assoc] at this ⊢
    exact this) this

theorem open_rel (h₀ : preX86_64 false s₀) (h₀' : preX86_64 false s₀') (hq : pubX86_64 s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.poly) fun _ _ => True := by
  have hp := APre.of _ h₀
  have hp' := APre.of _ h₀'
  have hfl := v.fold_le
  obtain ⟨_, hmid⟩ := openMid_taint v.fold_poly
  obtain ⟨_, hpost⟩ := openPost_taint v.fold_poly
  have mid := ((RelCT.taint (A := taintS)
    (P := fun s₁ s₂ => AfterF v.callee.fold s₀ s₁ ∧ AfterF v.callee.fold s₀' s₂) (τA false)
    (fun _ _ h => agreeA hp hp' hq h.1 h.2) hmid).wp (F₁ := AtIte v.callee.fold s₀)
    (F₂ := AtIte v.callee.fold s₀') fun _ _ h =>
      ⟨openMid_ok hfl v.poly hp h.1, openMid_ok hfl v.poly hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have post := RelCT.taint (A := taintS) (P := fun s₁ s₂ => After s₀ s₁ ∧ After s₀' s₂) (τ₁ false)
    (fun _ _ h => agree₁ hp hp' hq h.1 h.2) hpost
  have := (toPost_rel v hp hp' hq mid).seq post
  refine RelCT.of_exec open_exec ?_
  exact RelCT.of_exec (fun e => by
    cases e with | seq e₀ e => cases e with | seq eA e => cases e with | seq eC e => cases e with
    | seq eM e => cases e with | seq eI eP =>
    have := Exec.seq (Exec.seq e₀ (Exec.seq eA (Exec.seq eC (Exec.seq eM eI)))) eP
    simp only [List.append_assoc] at this ⊢
    exact this) this

end

end VG.Proof.ChaCha20Poly1305.X86_64
