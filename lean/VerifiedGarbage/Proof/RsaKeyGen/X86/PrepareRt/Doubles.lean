module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Double
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `w + 1` doublings of array 6 modulo the candidate, in a frame keeping the workspace pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86.Sieve (StackContext)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready phaseRanges phase_header phase_candidate)

/-- The frame's words are beyond every range of the workspace. -/
theorem stack_far {g : Geometry} {q : BitVec 32}
    (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) {o n : Nat} (fit : o + n ≤ g.L)
    {i : Nat} (hi : i < 20) : o + n ≤ ofs g.W (off (q.setWidth 64) 0 + BitVec.ofNat 64 i) := by
  have inside : (⟨q.setWidth 64, 20⟩ : Region).Contains (off (q.setWidth 64) 0 + BitVec.ofNat 64 i) 1 := by
    simp only [Region.Contains, off, BitVec.add_zero, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  have outside : ¬ (⟨g.W, g.L⟩ : Region).Contains (off (q.setWidth 64) 0 + BitVec.ofNat 64 i) 1 :=
    fun h => apart _ h inside
  simp only [Region.Contains] at outside
  simp only [ofs]
  omega

/-- The frame's first word is unchanged by writes to a range of the workspace. -/
theorem stack_read {g : Geometry} {q : BitVec 32}
    (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) {o n : Nat} (fit : o + n ≤ g.L)
    {m m' : Mem} (O : Outside g.W o n m m') :
    m'.readW (off (q.setWidth 64) 0) 32 = m.readW (off (q.setWidth 64) 0) 32 :=
  Mem.readW_congr fun _ hj => O _ (Or.inr (stack_far apart fit (by omega)))

/-- The frame's words are beyond every range a doubling writes. -/
theorem far_of_apart {g : Geometry} (v : g.Valid) {q : BitVec 32}
    (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    ∀ i < 4, ∀ r ∈ doubleRanges g, ofs g.W (off (q.setWidth 64) 0 + BitVec.ofNat 64 i) < r.1 ∨
      r.1 + r.2 ≤ ofs g.W (off (q.setWidth 64) 0 + BitVec.ofNat 64 i) := by
  intro i hi r mem
  obtain ⟨fit6, -, -, -⟩ := WitnessRt.fits v
  have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
    unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
  have fit : r.1 + r.2 ≤ g.L := by
    simp only [doubleRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> dsimp only <;> omega
  exact Or.inr (stack_far apart fit (by omega))

/-- A context kept through memory that changed only in ranges past the header. -/
theorem Context.keepWork {g : Geometry} (v : g.Valid) {s t : State} (C : Context g s)
    {rs : List Reg} (K : Keeps rs s t) (base : .edi ∉ rs)
    {ranges : List (Nat × Nat)} (W : WorkspaceFrame g ranges s.mem t.mem)
    (header : ∀ r ∈ ranges, 256 ≤ r.1) : Context g t := by
  have read {d : Nat} (fit : d + 4 ≤ 256) : w32 t.mem g.W d = w32 s.mem g.W d :=
    congrArg BitVec.toNat (W.read32 (Nat.le_trans fit v.headerFit)
      (fun r mem => Or.inl (Nat.le_trans fit (header r mem))))
  refine ⟨C.ws.of_keeps K, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, K.1 .edi base]; exact C.base
  · rw [read (by decide)]; exact C.width
  · rw [read (by decide)]; exact C.stride
  · intro j index
    rw [read (by omega)]; exact C.pointers j index

/-- The prepared state kept through writes to workspace ranges past the candidate and to the caller's stack. -/
theorem _root_.VG.Proof.RsaKeyGen.X86.PreparedR2.Ready.keepWorkOf {g : Geometry} (v : g.Valid)
    {c capacity : Nat} {p : BitVec 32} {s t : State} (S : Ready g c capacity p s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) (base : .edi ∉ rs)
    {ranges : List (Nat × Nat)} (W : WorkspaceFrame g ranges s.mem t.mem)
    (header : ∀ r ∈ ranges, 256 ≤ r.1) (candidate : ∀ r ∈ ranges, g.array 0 + 4 * g.words ≤ r.1)
    (F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem) : Ready g c capacity p t :=
  ⟨Context.keepWork v S.context K base W header,
    S.modulus.keep v W (fun r mem => Or.inl (by have := header r mem; omega))
      (fun r mem => Or.inl (candidate r mem)),
    S.caller.keepFrame K sp F, S.scratch.of_keeps K base sp⟩

/-- The prepared state kept through writes to the phase's ranges and the caller's stack. -/
theorem _root_.VG.Proof.RsaKeyGen.X86.PreparedR2.Ready.keepWork {g : Geometry} (v : g.Valid)
    {c capacity : Nat} {p : BitVec 32} {s t : State} (S : Ready g c capacity p s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) (base : .edi ∉ rs)
    (W : WorkspaceFrame g (phaseRanges g) s.mem t.mem)
    (F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem) : Ready g c capacity p t :=
  S.keepWorkOf v K sp base W (fun _ mem => phase_header g mem) (fun _ mem => phase_candidate g mem) F

/-- What a doubling writes is among the phase's ranges. -/
theorem doubleRanges_cover {g : Geometry} {m m' : Mem} (W : WorkspaceFrame g (doubleRanges g) m m') :
    WorkspaceFrame g (phaseRanges g) m m' := by
  refine W.cover fun r mem => ?_
  simp only [doubleRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · refine ⟨(g.array 2, accLen (VG.Impl.Bignum.X86.PublicContext.modulus g.w)), by simp [phaseRanges], Nat.le_refl _, ?_⟩
    change g.array 2 + (4 * g.words + 4) ≤ g.array 2 + 4 * (2 * (2 * g.w) + 1)
    unfold Geometry.words; omega
  · refine ⟨(g.array 6, 8 * g.w), by simp [phaseRanges], Nat.le_refl _, ?_⟩
    change g.array 6 + 4 * g.words ≤ g.array 6 + 8 * g.w
    unfold Geometry.words; omega

/-- Memory changed only in the frame keeps the workspace. -/
theorem frame_workspace {g : Geometry} {q : BitVec 32} {m m' : Mem} (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) {d : Nat} (fit : d + 4 ≤ 20)
    (O : Outside (q.setWidth 64) d 4 m m') :
    Frame [⟨q.setWidth 64, 20⟩] m m' ∧ WorkspaceFrame g [] m m' := by
  have F : Frame [⟨q.setWidth 64, 20⟩] m m' := by
    simpa only [off, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] using
      VG.Proof.Bignum.outside_frame (O.mono (o' := 0) (n' := 20) (by omega) (by omega)) (by decide)
  exact ⟨F, VG.Proof.RsaKeyGen.X86.workspace_of_frame F nowrap fun r mem => by
    obtain rfl := List.mem_singleton.mp mem; exact apart⟩

/-- The workspace pointer saved at the frame's base, and `w + 1` doublings to do. -/
theorem doublesArgs_ok {g : Geometry} (v : g.Valid) {a : State} {q : BitVec 32} (C : Context g a)
    (St : StackContext q a) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    WP isa (.block doublesArgs) a fun b =>
      Context g b ∧ Frame [⟨q.setWidth 64, 20⟩] a.mem b.mem ∧ WorkspaceFrame g [] a.mem b.mem ∧
      StackContext q b ∧ b.mem.readW (off (q.setWidth 64) 0) 32 = b.gpr .edi ∧
      b.gpr .esi = BitVec.ofNat 32 (g.w + 1) ∧ Keeps [.esi] a b := by
  rw [show doublesArgs = [.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 0) .edi] ++
    [.mov .esi (.mem (VG.Impl.Mont.X86.sc 48)), .alu .add .esi (.imm 1)] from rfl]
  refine WP.block_append (WP.mono (St.store 0 (by decide) .edi) fun e ⟨Me, Oe, Ke, Se⟩ => ?_)
  obtain ⟨Fe, We⟩ := frame_workspace C.ws.nowrap apart (by decide) Oe
  have Ce := Context.keepWork v C Ke (by decide) We fun _ mem => nomatch mem
  refine wp_movS (readSrc_ptr Ce.ws (r := .edi) (x := 0) (d := 48) Ce.base (by have := v.headerFit; omega))
    fun f F _ => wp_addS rfl fun b B _ => WP.block_nil ?_
  have K : Keeps [.esi] e b := (F.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = e.mem := by rw [B.mem, F.mem]
  refine ⟨Ce.keepMem K (by decide) Mb, by rw [Mb]; exact Fe, by rw [Mb]; exact We, Se.keep K (by decide),
    ?_, ?_, (Ke.mono (by decide)).trans K⟩
  · rw [Mb, Me, Mem.readW_writeW_self32, K.1 .edi (by decide), Ke.1 .edi (by decide)]
  · rw [B.gpr, F.gpr, Nat.zero_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    change (w32 e.mem g.W 48 + 1) % 2 ^ 32 = _
    rw [Ce.width]

/-- The doublings: array 6 times `2^N` modulo the candidate. -/
theorem loop_ok {g : Geometry} (v : g.Valid) {b : State} {c X N : Nat} {q : BitVec 32}
    (C : Context g b) (M : Modulus g c b.mem) (St : StackContext q b)
    (saved : b.mem.readW (off (q.setWidth 64) 0) 32 = b.gpr .edi)
    (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩)
    (value : val32 b.mem g.W (g.array 6) g.words = X % c) (positive : 0 < c)
    (count : b.gpr .esi = BitVec.ofNat 32 N) (hN : 0 < N) (bound : N < 2 ^ 32) :
    WP isa (.loop double .ne) b fun t =>
      Context g t ∧ Modulus g c t.mem ∧ StackContext q t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ N * X % c ∧ Outs g.W (doubleRanges g) b.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] b t := by
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop hN (fun j t =>
      Context g t ∧ Modulus g c t.mem ∧ StackContext q t ∧
      t.mem.readW (off (q.setWidth 64) 0) 32 = t.gpr .edi ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ j * X % c ∧ t.gpr .esi = BitVec.ofNat 32 (N - j) ∧
      Outs g.W (doubleRanges g) b.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] b t) ?_
    ⟨C, M, St, saved, by rw [value, Nat.pow_zero, Nat.one_mul], by rw [count, Nat.sub_zero],
      Outs.refl _ _ _, Keeps.refl _ _⟩) fun t ⟨Ct, Mt, St, _, Vt, _, Ot, Kt⟩ => ⟨Ct, Mt, St, Vt, Ot, Kt⟩
  rintro j t index ⟨Ct, Mt, Stt, sv, Vt, Et, Ot, Kt⟩
  refine WP.mono (double_ok v Ct Mt Stt sv (far_of_apart v apart) Vt (Nat.mod_lt _ positive) (k := N - j - 1)
    (by rw [Et]; congr 1; omega) (by omega)) fun u ⟨Cu, Mu, Su, svu, Vu, Eu, zu, Ou, Ku⟩ => ?_
  refine ⟨⟨Cu, Mu, Su, svu, ?_, by rw [Eu]; congr 1, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
  · rw [Vu, ← Nat.add_mod, Nat.pow_succ, Nat.mul_right_comm, Nat.mul_two]
  · rw [zu]
    congr 1
    exact decide_eq_decide.mpr (by omega)

theorem doubles_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (odd : c % 2 = 1) (top : 2 ^ (64 * g.w - 1) ≤ c)
    (value : val32 s.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w - 1)) :
    WP isa doubles s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 2 ^ g.w * 2 ^ (64 * g.w) % c ∧
      WorkspaceFrame g (phaseRanges g) s.mem t.mem ∧ Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t := by
  have sp := S.caller.sp
  have low := S.caller.low
  have C := S.context
  have nowrap := C.ws.nowrap
  have minW := v.minWidth
  have maxW := v.maxWidth
  have seedLt : 2 ^ (64 * g.w - 1) < c := by
    have even : 2 ^ (64 * g.w - 1) = 2 * 2 ^ (64 * g.w - 2) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega
  unfold doubles
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [sp]; omega) (NoSp.of_all (by rfl)) ?_
  have St : StackContext (s.gpr .esp - 20#32) (allocFrame 20 s) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; omega)
  have Ci : Context g (allocFrame 20 s) :=
    ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
      C.width, C.stride, C.pointers⟩
  have apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨(s.gpr .esp - 20#32).setWidth 64, 20⟩ := by
    have A := S.caller.stackFar.sub_right (below_sub (a := 20) (by decide) low)
    rw [← sp] at A
    exact A
  refine WP.seq (WP.mono (doublesArgs_ok v Ci St apart) fun b ⟨Cb, Fb, Wb, Sb, saved, count, Kb⟩ => ?_)
  have Mb : Modulus g c b.mem := S.modulus.keep v Wb (fun _ mem => nomatch mem) (fun _ mem => nomatch mem)
  have Vb : val32 b.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w - 1) % c := by
    have fit6 := (WitnessRt.fits v).1
    rw [Wb.val32 fit6 (fun _ mem => nomatch mem), allocFrame_mem, value, Nat.mod_eq_of_lt seedLt]
  refine WP.mono (loop_ok v Cb Mb Sb saved apart Vb (by omega) count (by omega) (by omega))
    fun t ⟨_, _, _, Vt, Ot, Kt⟩ => ?_
  have Kall : Keeps VG.Proof.Mont.X86.Dynamic.powerClob (allocFrame 20 s) t :=
    (Kb.mono (by decide)).trans (Kt.mono (by decide))
  have K : Keeps VG.Proof.Mont.X86.Dynamic.powerClob s (freed 20 t) :=
    VG.Proof.RsaKeyGen.X86.FilterStack.freed_keeps Kall (by decide)
  have fitR : ∀ r ∈ doubleRanges g, r.1 + r.2 ≤ g.L := fun r mem => by
    obtain ⟨fit6, -, -, -⟩ := WitnessRt.fits v
    have a26 : g.array 2 + 4 * g.words + 4 ≤ g.array 6 := by
      unfold Geometry.array Geometry.words Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes; omega
    simp only [doubleRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> dsimp only <;> omega
  have W : WorkspaceFrame g (phaseRanges g) s.mem (freed 20 t).mem := by
    rw [freed_mem]
    exact (Wb.mono fun _ mem => nomatch mem).trans (doubleRanges_cover (WorkspaceFrame.of_outs nowrap Ot))
  have F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem (freed 20 t).mem := by
    rw [freed_mem]
    refine Frame.trans (Fb.sub fun r mem => ?_) ((workspaceGlobalFrame Ot fitR).mono
      fun r mem => List.mem_append_left _ mem)
    obtain rfl := List.mem_singleton.mp mem
    refine ⟨below p 80, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [sp]
    exact below_sub (sp := p) (a := 20) (b := 80) (by decide) low
  refine ⟨S.keepWork v K (by decide) (by decide) W F, ?_, W, F, K⟩
  rw [freed_mem, Vt, ← Nat.pow_add, ← Nat.pow_add]
  congr 2
  omega

end VG.Proof.RsaKeyGen.X86.PrepareRt
