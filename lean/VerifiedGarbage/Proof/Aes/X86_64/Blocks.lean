module

public import VerifiedGarbage.Impl.Aes.X86_64.Blocks
public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Engine
public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Impl.Aes.X86_64.Blocks
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Bitsliced AES on whole blocks on x86-64

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86_64.encryptBlocks` and `decryptBlocks` against the contracts of
`Spec/Aes/Contract.lean`, through `blocksX86_64`. The blocks go in batches of
up to eight, through the buffer (`Sse/Engine.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the return address on the stack, and
`data` may not wrap around the end of the address space. `rounds` is 10, 12
or 14. The pointers, `rounds` and `n` are public; the key schedule and the
data are secret. -/
def blocksX86_64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).map
        (f (s.gpr .rsi).toNat (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- `blocksX86_64` without the scratch buffer, for the implementations of
encryption that never touch it (`vg_aes_encrypt_blocks_aesni`,
`vg_aes_encrypt_blocks_vaes`): their callers need not set aside its 2048
bytes. `r8` is still public. -/
def blocksX86_64F (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let data : Region := ⟨s.gpr .rdx, 16 * (s.gpr .rcx).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧ ret.Disjoint data ∧
    (s.gpr .rdx).toNat + 16 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := (blocksX86_64 f).post
  pub := (blocksX86_64 f).pub

end VG.Proof.Aes

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Aes.X86_64 VG.Impl.Aes.X86_64.Sse VG.Proof.Aes VG.Proof.Aes.X86_64.Sse
open VG.Proof.Aes.Memory (Processed)

/-- A batch's code computes `f` on the buffer. -/
def CryptOk (c : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {b : Addr} {nr : Nat} {w : List Byte} {S : Nat → Spec.Aes.State} {s : State}, BatchPre b nr w S s →
    WP isa c s (BatchPost b nr w (fun k => f nr w (S k)) s)

/-- The registers the functions keep. -/
abbrev Kept (x : Reg) : Prop := x ≠ .rax ∧ x ≠ .rcx ∧ x ≠ .rdi ∧ x ≠ .r8 ∧ x ≠ .r9 ∧ x ≠ .r10 ∧ x ≠ .r11

/-- The arguments of a run over `n` blocks at `D`. -/
structure BP (b D : Addr) (n nr : Nat) (s₀ : State) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  n64 : n < 2 ^ 64
  inD : ⟨D, 16 * n⟩ ∈ s₀.wr
  disj : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 1480⟩
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 nr

/-- After `k` blocks. -/
structure BI (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s₀ : State) (b D : Addr) (n nr : Nat) (w : List Byte)
    (k : Nat) (s : State) : Prop where
  ready : Ready b nr w s.mem s.rd s.wr
  r9 : s.gpr .r9 = b
  rcx : s.gpr .rcx = D + BitVec.ofNat 64 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - k)
  gpr : ∀ x, Kept x → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨D, 16 * n⟩, ⟨b, 1480⟩] s₀.mem s.mem
  done : Processed s₀.mem s.mem D n k fun i => f nr w (Spec.Aes.stateAt s₀.mem (D + BitVec.ofNat 64 (16 * i)))

theorem data_sub (D : Addr) {n k : Nat} (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) :
    Region.Sub ⟨D + BitVec.ofNat 64 (16 * k), 16⟩ ⟨D, 16 * n⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hx
  have := (x - D).isLt
  omega

/-- The buffer's blocks are the data's. -/
theorem bufS_of {s₁ s : State} {b p : Addr} {t : Nat} (h : CI s₁ b p t t s) {i : Nat} (hi : i < t) :
    bufS s.mem b i = Spec.Aes.stateAt s₁.mem (p + BitVec.ofNat 64 (16 * i)) := state_ext fun y hy => by
  rw [bufS, Spec.Aes.stateAt, Spec.Aes.stateAt, getD_ofFn _ hy, getD_ofFn _ hy, h.buf i hi y hy, BitVec.add_assoc,
    ← BitVec.ofNat_add]

variable {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {b D : Addr} {n nr : Nat} {w : List Byte}

theorem batch_ok {c : Prog isa} (hc : CryptOk c f) (hp : BP b D n nr s₀) {k : Nat} (hk : k < n) {s : State}
    (h : BI f s₀ b D n nr w k s) :
    WP isa (blocksBatch c) s fun s' => ∃ t, 0 < t ∧ k + t ≤ n ∧ BI f s₀ b D n nr w (k + t) s' ∧
      X86_64.eval .ne s' = some (decide (n - (k + t) ≠ 0)) := by
  have hwrap := hp.wrap
  have h16 : 16 * n ≤ 2 ^ 64 := by omega
  have hn64 := hp.n64
  obtain ⟨t, ht⟩ : ∃ t, t = min 8 (n - k) := ⟨_, rfl⟩
  have ht8 : t ≤ 8 := by omega
  have ht0 : 0 < t := by omega
  have hkt : k + t ≤ n := by omega
  have hsub : ∀ i < t, Region.Disjoint ⟨D + BitVec.ofNat 64 (16 * k) + BitVec.ofNat 64 (16 * i), 16⟩ (bufR b) := by
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * k + 16 * i = 16 * (k + i) by omega]
    exact (hp.disj.sub_left (data_sub D h16 (by omega))).sub_right (bufR_sub b)
  have hdD : Region.Disjoint (bufR b) ⟨D, 16 * n⟩ := (hp.disj.sub_right (bufR_sub b)).symm
  refine WP.seq (WP.block_append (WP.mono (batchSize_ok (r := n - k) (by omega) h.r8)
    fun s1 ⟨rdi1, r101, rax1, g1, m1, rd1, wr1, _⟩ => ?_))
  rw [← ht] at rdi1 r101
  refine WP.mono (Q := CI s1 b (D + BitVec.ofNat 64 (16 * k)) t 0) ?_ fun s2 h2 => ?_
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, readSrc, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, ?_, ?_, fun x a c d => ?_, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · simp only [gpr_setReg, ite_true, g1 _ (show Reg.rcx ≠ .rax by decide) (by decide) (by decide), h.rcx]; simp
    · simp only [gpr_setReg, reduceCtorEq, ite_false, rax1, h.r9]; rfl
    · simp only [gpr_setReg, reduceCtorEq, ite_false, r101]; rfl
    · simp only [gpr_setReg, d, ite_false]
  have hbuf : ∀ i < 8, InRegions s1.wr (bufAddr b i) 16 := fun i hi => by rw [wr1]; exact h.ready.bufIn hi
  refine WP.seq (WP.mono (copyIn_loop ht8 ht0 (fun i hi => ?_) hbuf hsub h2) fun s3 h3 => ?_)
  · rw [rd1, wr1, h.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ hp.inD, Offset.contains_base _ (by omega) (by omega)⟩
  have g3 : ∀ x, Kept x ∨ x = .rcx ∨ x = .r8 ∨ x = .r9 ∨ x = .rdi → x ≠ .rdi → s3.gpr x = s.gpr x := by
    intro x hx hne
    have hx' : x ≠ .rax ∧ x ≠ .r10 ∧ x ≠ .r11 := by
      rcases hx with hx | rfl | rfl | rfl | rfl
      · exact ⟨hx.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2⟩
      all_goals decide
    rw [h3.gpr x hx'.1 hx'.2.1 hx'.2.2, g1 x hx'.1 hx'.2.1 hne]
  have r93 : s3.gpr .r9 = b := by rw [g3 .r9 (by simp) (by decide), h.r9]
  have hrsi : Kept .rsi := by decide
  have hready3 : Ready b nr w s3.mem s3.rd s3.wr := by
    have f3 := h3.frame
    rw [m1] at f3
    rw [h3.rd, h3.wr, rd1, wr1]
    refine h.ready.frame f3 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨Offset.disjoint _ (.inr (by decide)) (by decide) (by decide),
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)⟩
  refine WP.seq (WP.mono (hc (S := bufS s3.mem b) ⟨hready3, r93, by rw [g3 .rsi (.inl hrsi) (by decide), h.gpr _ hrsi, hp.rsi],
    bufIs_bufS _ _⟩) fun s4 h4 => ?_)
  have r84 : s4.gpr .r8 = BitVec.ofNat 64 (n - k) := by
    rw [h4.gpr _ (by decide) (by decide), g3 .r8 (by simp) (by decide), h.r8]
  have rdi4 : s4.gpr .rdi = BitVec.ofNat 64 t := by
    rw [h4.gpr _ (by decide) (by decide), h3.gpr _ (by decide) (by decide) (by decide), rdi1]
  refine WP.seq (WP.mono (batchSize_ok (r := n - k) (by omega) r84) fun s5 ⟨rdi5, r105, rax5, g5, m5, rd5, wr5, _⟩ => ?_)
  rw [← ht] at rdi5 r105
  have r94 : s4.gpr .r9 = b := by rw [h4.gpr _ (by decide) (by decide), r93]
  have f35 : Frame [⟨b, 416⟩] s3.mem s5.mem := by rw [m5]; exact h4.frame
  have f5 : Frame [⟨b, 1480⟩] s.mem s5.mem := by
    have := h3.frame
    rw [m1] at this
    exact (this.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, by rw [List.mem_singleton.mp hr]; exact bufR_sub b⟩).trans
      (f35.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, by rw [List.mem_singleton.mp hr]; exact low416_sub b⟩)
  have wr5' : s5.wr = s₀.wr := by rw [wr5, h4.wr, h3.wr, wr1, h.wr]
  have done5 : Processed s₀.mem s5.mem D n k fun i => f nr w (Spec.Aes.stateAt s₀.mem (D + BitVec.ofNat 64 (16 * i))) :=
    h.done.frame f5 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.disj) h16
  have hbufF : ∀ i < t, ∀ x < 16, s5.mem (bufAddr b i + BitVec.ofNat 64 x) =
      (f nr w (Spec.Aes.stateAt s₀.mem (D + BitVec.ofNat 64 (16 * (k + i))))).getD x 0 := by
    intro i hi x hx
    rw [m5, h4.buf i (by omega) x hx, ← h.done.original (by omega) (by omega)]
    dsimp only
    rw [bufS_of h3 hi, m1, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 16 * k + 16 * i = 16 * (k + i) by omega]
  refine WP.seq (WP.mono (copyOut_loop (s₁ := s5) (m₀ := s₀.mem) (F := fun i => f nr w (Spec.Aes.stateAt s₀.mem (D + BitVec.ofNat 64 (16 * i))))
    ht8 ht0 hkt h16 (by rw [wr5']; exact hp.inD)
    (fun i hi => by rw [wr5, h4.wr, h3.wr]; exact hbuf i hi) hdD hbufF
    ⟨?_, ?_, ?_, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, by simpa using done5⟩) fun s6 h6 => ?_)
  · rw [g5 _ (by decide) (by decide) (by decide), h4.gpr _ (by decide) (by decide), g3 .rcx (by simp) (by decide), h.rcx]; simp
  · rw [rax5, r94, bufAddr_eq]
  · rw [r105]; simp
  have rdi6 : s6.gpr .rdi = BitVec.ofNat 64 t := by rw [h6.gpr _ (by decide) (by decide) (by decide), rdi5]
  have r86 : s6.gpr .r8 = BitVec.ofNat 64 (n - k) := by
    rw [h6.gpr _ (by decide) (by decide) (by decide), g5 _ (by decide) (by decide) (by decide), r84]
  have ecnt : s6.gpr .r8 - s6.gpr .rdi = BitVec.ofNat 64 (n - (k + t)) := by
    rw [r86, rdi6, show n - k = n - (k + t) + t by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have g6 : ∀ x, Kept x ∨ x = .r9 → s6.gpr x = s.gpr x := by
    intro x hx
    have hx' : x ≠ .rax ∧ x ≠ .rcx ∧ x ≠ .rdi ∧ x ≠ .r10 ∧ x ≠ .r11 := by
      rcases hx with hx | rfl
      · exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2⟩
      · decide
    rw [h6.gpr x hx'.1 hx'.2.2.2.1 hx'.2.1, g5 x hx'.1 hx'.2.2.2.1 hx'.2.2.1, h4.gpr x hx'.1 hx'.2.2.2.1,
      g3 x (by rcases hx with hx | rfl; exact .inl hx; simp) hx'.2.2.1]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some, ecnt,
    Option.some.injEq, exists_eq_left']
  refine ⟨t, ht0, hkt, ⟨?_, ?_, ?_, ?_, fun x hx => ?_, ?_, ?_, ?_, h6.done⟩, ?_⟩
  · have hr5 : Ready b nr w s5.mem s5.rd s5.wr := by rw [m5, rd5, wr5]; exact h4.ready
    have := hr5.frame h6.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨(hp.disj.sub_right (sub_scratch b (by decide))).symm, (hp.disj.sub_right (sub_scratch b (by decide))).symm⟩
    rw [← h6.rd, ← h6.wr] at this
    exact this
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; rw [g6 .r9 (.inr rfl), h.r9]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h6.rcx
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, hx.2.2.2.1, ite_false]; rw [g6 x (.inl hx), h.gpr x hx]
  · exact h6.rd.trans (rd5.trans (h4.rd.trans (h3.rd.trans (rd1.trans h.rd))))
  · exact h6.wr.trans wr5'
  · exact h.frame.trans ((f5.mono fun r hr => List.mem_cons_of_mem _ hr).trans (h6.frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self))
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

/-- The whole function, around `c`. -/
theorem blocks_wp {c : Prog isa} (hc : CryptOk c f) {s₀ : State} (hs : (blocksX86_64 f).pre s₀) :
    WP isa (blocks c) s₀ fun s' => gprPreserved s₀ s' ∧ (blocksX86_64 f).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dRD, dRS, wrap, hnr⟩ := hs
  obtain ⟨nr, hnr'⟩ : ∃ nr, nr = (s₀.gpr .rsi).toNat := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = (s₀.gpr .rcx).toNat := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = s₀.gpr .rdx := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = s₀.gpr .r8 := ⟨_, rfl⟩
  rw [← hn, ← hD] at dKD dDS dRD wrap
  rw [← hb] at dKS dDS dRS
  rw [← hnr'] at hnr
  have hn64 : n < 2 ^ 64 := by rw [hn]; exact (s₀.gpr .rcx).isLt
  have h16 : 16 * n ≤ 2 ^ 64 := by omega
  have scr : Region.Sub ⟨b, 1480⟩ ⟨b, 2048⟩ := fun x hx => by simp only [Region.Contains] at hx ⊢; omega
  have hsi : s₀.gpr .rsi = BitVec.ofNat 64 nr := by rw [hnr']; simp
  have post : ∀ s' : State, (∀ x, Kept x → s'.gpr x = s₀.gpr x) → Frame [⟨D, 16 * n⟩, ⟨b, 1480⟩] s₀.mem s'.mem →
      Processed s₀.mem s'.mem D n n (fun i => f nr (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * (nr + 1)))
        (Spec.Aes.stateAt s₀.mem (D + BitVec.ofNat 64 (16 * i)))) →
      gprPreserved s₀ s' ∧ (blocksX86_64 f).post s₀ s' := by
    intro s' hg hf hp
    refine ⟨⟨fun r hr => hg r ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · refine hf.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRD
      · exact dRS.sub_right scr
    · show Spec.Aes.statesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = _
      rw [← hn, ← hD, hp.statesAt, Spec.Aes.statesAt, List.map_map, ← hnr']
      rfl
  refine WP.seq ?_
  have key : ∃ s1, runBlock isa [.mov .r9 (.reg .r8), .mov .r8 (.reg .rcx), .mov .rcx (.reg .rdx), .alu .test .r8 (.reg .r8)] s₀ =
      some s1 ∧ s1.zf = some (decide (n = 0)) ∧ s1.gpr .r9 = b ∧ s1.gpr .r8 = BitVec.ofNat 64 n ∧ s1.gpr .rcx = D ∧
      (∀ x, x ≠ .r9 → x ≠ .r8 → x ≠ .rcx → s1.gpr x = s₀.gpr x) ∧ s1.mem = s₀.mem ∧ s1.rd = s₀.rd ∧ s1.wr = s₀.wr := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.map_some,
      Option.bind_some, gpr_setReg, reduceCtorEq, ite_false, ite_true, BitVec.and_self, Option.some.injEq, exists_eq_left',
      gpr_arithFlags, zf_arithFlags]
    have en : s₀.gpr .rcx = BitVec.ofNat 64 n := by rw [hn]; simp
    refine ⟨by rw [en, beq_zero hn64], hb.symm, en, hD.symm, fun x a c d => ?_, rfl, rfl, rfl⟩
    simp only [a, c, d, ite_false]
  obtain ⟨s1, e1, z1, r91, r81, rcx1, g1, m1, rd1, wr1⟩ := key
  refine WP.of_runBlock ⟨s1, e1, ?_⟩
  refine WP.ite (decide (n = 0)) (by simp [X86_64.eval, z1]) (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : n = 0 := by simpa using h0
    refine WP.block_nil (post s1 (fun x hx => g1 x hx.2.2.2.2.1 hx.2.2.2.1 hx.2.1) (by rw [m1]; exact Frame.refl _ _) ?_)
    rw [m1]
    intro i hi
    omega
  have h0 : n ≠ 0 := by simpa using h0
  have hkp : KPre b (s₀.gpr .rdi) nr s1 := by
    refine ⟨r91, g1 _ (by decide) (by decide) (by decide), by rw [g1 _ (by decide) (by decide) (by decide), hsi], hnr, .inl ?_, ?_,
      dKS.sub_right scr⟩
    · rw [wr1, hwr, hb]; simp
    · rw [rd1, hrd]; simp
  have hbp : BP b D n nr s₀ := ⟨wrap, hn64, by rw [hwr, hD, hn]; simp, dDS.sub_right scr, hsi⟩
  refine WP.seq (WP.mono (keys_ok hkp) fun s2 h2 => ?_)
  have f2 : Frame [⟨b, 1480⟩] s₀.mem s2.mem := by rw [← m1]; exact h2.frame
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * (nr + 1))
  have hI0 : BI f s₀ b D n nr w 0 s2 := by
    have hr2 := h2.ready
    rw [m1] at hr2
    refine ⟨hr2, ?_, ?_, ?_, fun x hx => ?_, h2.rd.trans rd1, h2.wr.trans wr1, f2.mono fun r hr => List.mem_cons_of_mem _ hr, ?_⟩
    · rw [h2.gpr _ (by decide) (by decide) (by decide), r91]
    · rw [h2.gpr _ (by decide) (by decide) (by decide), rcx1]; simp
    · rw [h2.gpr _ (by decide) (by decide) (by decide), r81]; rfl
    · rw [h2.gpr x hx.1 hx.2.2.2.2.2.1 hx.2.2.1, g1 x hx.2.2.2.2.1 hx.2.2.2.1 hx.2.1]
    · exact (Processed.refl s₀.mem D n _).frame f2
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hbp.disj) h16
  let I : Nat → State → Prop := fun c s => ∃ k, c = n - k ∧ k < n ∧ BI f s₀ b D n nr w k s
  refine WP.mono (Q := BI f s₀ b D n nr w n) ?_ fun s3 h3 => post s3 h3.gpr h3.frame h3.done
  refine WP.loop (M := isa) I ?_ n s2 ⟨0, rfl, by omega, hI0⟩
  rintro c' s' ⟨k, rfl, hk, hs'⟩
  refine WP.mono (batch_ok hc hbp hk hs') fun s4 ⟨t, ht0, hkt, h4, hz⟩ => ?_
  by_cases hl : n - (k + t) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show k + t = n by omega] at h4
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, k + t, rfl, by omega, h4⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := blocks_wp (fun h => encrypt8_ok h) hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := blocks_wp (fun h => decrypt8_ok h) hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

theorem encryptBlocks_verified :
    Verified X86_64.target encryptBlocks (Proof.Aes.encryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct encryptBlocks_correct encryptBlocks_ct (by
    sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified :
    Verified X86_64.target decryptBlocks (Proof.Aes.decryptBlocksRoundsContract X86_64.abi) :=
  Verified.of_correct decryptBlocks_correct decryptBlocks_ct (by
    sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.Aes.X86_64
