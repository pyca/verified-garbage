module

public import VerifiedGarbage.Impl.Mcdt.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Impl.Mcdt.X86_64
meta import VerifiedGarbage.Proof.MlKem.X86_64.Rel

/-!
# A call inside Intel's MXCSR prologue and epilogue (x86-64): what it does

`mcdtCall n c` (`Impl/Mcdt/X86_64.lean`) runs `c` as `WP.call_mx` does a
call of it, from a state at its entry that differs from the caller's only
in `rax`, `rbx`, the stack pointer, 24 bytes lower, those 24 bytes, and the
frame's 16 at the head of the writable regions (`EntryOf`); and returns
with the caller's callee-saved registers, and with MXCSR the caller's but
for its reserved bits (`WP.mcdtCall`), whatever `c` does with MXCSR's
status flags: `c` keeps `rbx`, which holds the saved MXCSR. `RelCT.mcdtCall`
relates two runs of it, as `RelCT.callEx` does two calls.
-/

@[expose] public section

namespace VG.Proof.Mcdt.X86_64

open VG VG.X86_64 VG.Impl.Mcdt.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep taintRel)

theorem ea_sp (s : State) (d : Nat) : s.ea (sp d) = s.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp]
  congr 1

theorem and_ffff_hi (x : BitVec 32) : (x &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
  simp only [Nat.testBit_two_pow_sub_one]
  simp

theorem contains_off (b : Addr) {d n len : Nat} (h : d + n ≤ len) (hl : len < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact h

/-- The prologue, from a state whose 8 bytes at `rsp` are writable: MXCSR
but for its reserved bits to `rbx`, `0x1FBF` to MXCSR. -/
theorem pro_ok {s : State} {F : Region} (hF : F ∈ s.wr) (h0 : F.Contains (s.gpr .rsp) 4)
    (h4 : F.Contains (s.gpr .rsp + 4#64) 4) :
    WP isa (.block pro) s fun s' => (s'.gpr .rbx = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧
      s'.mxcsr = 0x1FBF ∧ s'.mem = (s.mem.writeW (s.gpr .rsp) s.mxcsr).writeW (s.gpr .rsp + 4#64) (0x1FBF : BitVec 32)) ∧
      Keep [.rbx, .rax] s s' := by
  have w0 : InRegions s.wr (s.gpr .rsp) 4 := ⟨F, hF, h0⟩
  have w4 : InRegions s.wr (s.gpr .rsp + 4#64) 4 := ⟨F, hF, h4⟩
  have l0 : InRegions (s.rd ++ s.wr) (s.gpr .rsp) 4 := ⟨F, List.mem_append_right _ hF, h0⟩
  have l4 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 4#64) 4 := ⟨F, List.mem_append_right _ hF, h4⟩
  refine WP.keep [.rbx, .rax] ?_ rfl
  xrun [pro, ea_sp, w0, w4, l0, l4, Mem.readW_writeW_self32]

/-- The epilogue, from a state whose 4 bytes at `rsp` are writable and whose
`rbx` holds a value of MXCSR but for its reserved bits: MXCSR from it. -/
theorem epi_ok {s : State} {F : Region} {v : BitVec 32} (hF : F ∈ s.wr) (h0 : F.Contains (s.gpr .rsp) 4)
    (hv : s.gpr .rbx = (v &&& 0xFFFF).setWidth 64) :
    WP isa (.block epi) s fun s' => s'.mxcsr = v &&& 0xFFFF ∧
      s'.mem = s.mem.writeW (s.gpr .rsp) ((s.gpr .rbx).setWidth 32) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have w0 : InRegions s.wr (s.gpr .rsp) 4 := ⟨F, hF, h0⟩
  have l0 : InRegions (s.rd ++ s.wr) (s.gpr .rsp) 4 := ⟨F, List.mem_append_right _ hF, h0⟩
  xrun [epi, ea_sp, w0, l0, hv, Mem.readW_writeW_self32, and_ffff_hi]

/-- What the state at the entry of `c` is, from the caller's `s`. -/
structure EntryOf (s e : State) : Prop where
  gpr : ∀ r, r ≠ .rsp → r ≠ .rax → r ≠ .rbx → e.gpr r = s.gpr r
  rsp : e.gpr .rsp = s.gpr .rsp - 24
  mem : Frame [below (s.gpr .rsp) 24] s.mem e.mem
  rd : e.rd = s.rd
  wr : e.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 16, 16⟩ :: s.wr

theorem cont (S : Addr) {a n m : Nat} (h1 : n ≤ a) (h2 : a ≤ m) (h3 : m < 2 ^ 64) :
    (below S m).Contains (S - BitVec.ofNat 64 a) n := by
  simp only [Region.Contains]
  rw [Offset.sub_ofNat_sub_sub_ofNat S h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sub_below (S : Addr) {a b n : Nat} (h : n + a ≤ b) (hb : b < 2 ^ 64) :
    Region.Sub (below (S - BitVec.ofNat 64 a) n) (below S b) := fun x hx => by
  have := Offset.below_sub_below (S - BitVec.ofNat 64 a) (m := n) (d := a) (r := b) h hb x hx
  rwa [BitVec.sub_add_cancel] at this

/-- Two regions below `S`, the second below the first. -/
theorem disj (S : Addr) {a n b m : Nat} (h1 : n ≤ a) (h2 : a + m ≤ b) (h3 : b ≤ S.toNat) :
    Region.Disjoint ⟨S - BitVec.ofNat 64 a, n⟩ ⟨S - BitVec.ofNat 64 b, m⟩ := by
  intro x hx hy
  simp only [Region.Contains] at hx hy
  have := S.isLt
  bv_omega

theorem popReg2 (u : State) : (popReg u .rbx 2).gpr .rbx = u.mem.readW (u.gpr .rsp + 8) 64 := by
  simp [popReg, State.setReg]


/-- What the frame's push and the prologue leave, from the caller's `s`. -/
structure Pro (s s₃ : State) : Prop where
  ent : EntryOf s s₃.callEntry
  rd : s₃.rd = s.rd
  wr : s₃.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 16, 16⟩ :: s.wr
  rsp : s₃.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 16
  rbx : s₃.gpr .rbx = (s.mxcsr &&& 0xFFFF).setWidth 64
  gpr : ∀ r, r ≠ .rsp → r ≠ .rax → r ≠ .rbx → s₃.gpr r = s.gpr r
  mem : Frame [below (s.gpr .rsp) 16] s.mem s₃.mem
  /-- The caller's `rbx`, from the frame's first push. -/
  saved : s₃.mem.readW (s.gpr .rsp - 8) 64 = s.gpr .rbx

theorem pro_run {s : State} (hS : 24 ≤ (s.gpr .rsp).toNat) :
    WP isa (.block pro) (pushed [.rbx, .rbx] s) (Pro s) := by
  have hlt := (s.gpr .rsp).isLt
  generalize hSdef : s.gpr .rsp = S at *
  let F : Region := ⟨S - BitVec.ofNat 64 16, 16⟩
  have s1sp : (pushed [.rbx, .rbx] s).gpr .rsp = S - BitVec.ofNat 64 16 := by
    rw [pushed_rsp, hSdef]; rfl
  have s1wr : (pushed [.rbx, .rbx] s).wr = F :: s.wr := by rw [pushed_wr, hSdef]; rfl
  have hF : F ∈ (pushed [.rbx, .rbx] s).wr := by rw [s1wr]; exact List.mem_cons_self
  have c0 : F.Contains (S - BitVec.ofNat 64 16) 4 := by
    simpa using contains_off (S - BitVec.ofNat 64 16) (d := 0) (n := 4) (len := 16) (by omega) (by omega)
  have c4 : F.Contains (S - BitVec.ofNat 64 16 + 4#64) 4 :=
    contains_off (S - BitVec.ofNat 64 16) (d := 4) (n := 4) (len := 16) (by omega) (by omega)
  obtain ⟨pf, pv⟩ := pushRegs_mem s [.rbx, .rbx] (by decide) (by rw [hSdef]; simp; omega)
  rw [hSdef] at pf pv
  have hrbx : (pushed [.rbx, .rbx] s).mem.readW (S - 8) 64 = s.gpr .rbx := pv 0 (by decide)
  refine WP.mono (pro_ok (s := pushed [.rbx, .rbx] s) hF (by rw [s1sp]; exact c0)
    (by rw [s1sp]; exact c4)) fun s₃ ⟨⟨hbx, hmx, hm3⟩, k3⟩ => ?_
  have s3sp : s₃.gpr .rsp = S - BitVec.ofNat 64 16 := by rw [k3.gpr (by decide), s1sp]
  have e12 : S - BitVec.ofNat 64 16 + 4#64 = S - BitVec.ofNat 64 12 := by bv_omega
  have e24 : S - BitVec.ofNat 64 16 - 8 = S - BitVec.ofNat 64 24 := by bv_omega
  have hm3' : s₃.mem = ((pushRegs s [.rbx, .rbx]).mem.writeW (S - BitVec.ofNat 64 16) s.mxcsr).writeW
      (S - BitVec.ofNat 64 12) (0x1FBF : BitVec 32) := by
    rw [hm3, s1sp, e12, pushed_mxcsr]; rfl
  have f13 : Frame [below S 16] s.mem s₃.mem := by
    rw [hm3']
    refine ((pf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (cont S (a := 16) (n := 4) (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (cont S (a := 12) (n := 4) (by omega) (by omega) (by omega))
    rw [List.mem_singleton] at hr; subst hr
    exact fun _ h => h
  have f3 : Frame [⟨S - BitVec.ofNat 64 16, 8⟩] (pushed [.rbx, .rbx] s).mem s₃.mem := by
    rw [hm3', ← e12]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using contains_off (S - BitVec.ofNat 64 16) (d := 0) (n := 4) (len := 8) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (S - BitVec.ofNat 64 16) (d := 4) (n := 4) (len := 8) (by omega) (by omega))
  refine ⟨⟨fun r h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_⟩ <;>
    try simp only [hSdef]
  · rw [State.callEntry_gpr _ h1, k3.gpr (by simp [h2, h3]), pushed_gpr _ _ h1]
  · rw [State.callEntry_rsp, s3sp, e24]; rfl
  · rw [State.callEntry_mem, s3sp, e24]
    refine (f13.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (cont S (a := 24) (n := 8) (by omega) (by omega) (by omega))
    rw [List.mem_singleton] at hr; subst hr
    exact below_sub (by omega) (by omega)
  · rw [State.callEntry_rd, k3.2.1, pushed_rd]
  · rw [State.callEntry_wr, k3.2.2, s1wr]
  · rw [k3.2.1, pushed_rd]
  · rw [k3.2.2, s1wr]
  · exact s3sp
  · rw [hbx, pushed_mxcsr]
  · rw [k3.gpr (by simp [h2, h3]), pushed_gpr _ _ h1]
  · exact f13
  · rw [f3.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disj S (a := 8) (n := 8) (b := 16) (m := 8) (by omega) (by omega) (by omega)) (by decide)]
    exact hrbx

/-- Covers into the regions with the frame's. -/
theorem covers_frame {rd wr rd' wr' : List Region} (F : Region) (hc : Covers (rd ++ wr) (rd' ++ wr'))
    (hw : Covers wr wr') : Covers (rd ++ wr) (rd' ++ F :: wr') ∧ Covers wr (F :: wr') :=
  ⟨hc.trans (Covers.of_mem fun r hr => by
      simp only [List.mem_append, List.mem_cons] at hr ⊢
      rcases hr with h | h
      exacts [.inl h, .inr (.inr h)]),
    hw.trans (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)⟩

/-- `mcdtCall n c` runs `c` from a state at its entry that `EntryOf` describes, with its permissions
narrowed to `rd` and `wr` (disjoint from the frame), and returns as `WP.call_mx` says a call does,
with memory changed only within `wr` and the stack the call and the frame use; but `rbx`, which `c`
may leave other than the caller's in the state its postcondition describes, and the memory of the
frame; and with MXCSR the caller's but for its reserved bits. -/
theorem WP.mcdtCall {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) {s : State} (hS : 8 * c.depth + 24 ≤ (s.gpr .rsp).toNat) {rd wr : List Region}
    (hpre : ∀ e, EntryOf s e → k.pre (e.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (hdj : ∀ r ∈ wr, (below (s.gpr .rsp) 16).Disjoint r) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * c.depth + 24)]) s.mem s'.mem →
      (∃ e s₂, EntryOf s e ∧ Frame [below (s.gpr .rsp) 16] s₂.mem s'.mem ∧
        (∀ r, r ≠ .rsp → r ≠ .rbx → s₂.gpr r = s'.gpr r) ∧ k.post (e.withRegions rd wr) s₂) →
      s'.mxcsr = s.mxcsr &&& 0xFFFF → Q s') :
    WP isa (mcdtCall n c) s Q := by
  have hlt := (s.gpr .rsp).isLt
  unfold VG.Impl.Mcdt.X86_64.mcdtCall
  refine WP.frame (by simp) (by decide) (by decide) (by simp; omega) ?_
  refine WP.seq (WP.mono (pro_run (s := s) (by omega)) fun s₃ h3 => ?_)
  generalize hSdef : s.gpr .rsp = S at *
  have s1sp : (pushed [.rbx, .rbx] s).gpr .rsp = S - BitVec.ofNat 64 16 := by
    rw [pushed_rsp, hSdef]; rfl
  have s1wr : (pushed [.rbx, .rbx] s).wr = ⟨S - BitVec.ofNat 64 16, 16⟩ :: s.wr := by rw [pushed_wr, hSdef]; rfl
  have c0 : (⟨S - BitVec.ofNat 64 16, 16⟩ : Region).Contains (S - BitVec.ofNat 64 16) 4 := by
    simpa using contains_off (S - BitVec.ofNat 64 16) (d := 0) (n := 4) (len := 16) (by omega) (by omega)
  have e8 : S - BitVec.ofNat 64 16 + 8 = S - 8 := by bv_omega
  obtain ⟨hc3, hw3⟩ := covers_frame ⟨S - BitVec.ofNat 64 16, 16⟩ hc hw
  have r3 := h3.rd
  have w3 := h3.wr
  have sp3 := h3.rsp
  have m3 := h3.mem
  have sv3 := h3.saved
  rw [hSdef] at w3 sp3 m3 sv3
  rw [← r3, ← w3] at hc3; rw [← w3] at hw3
  refine WP.seq (WP.call_mx hv hsp (by omega) (s := s₃) (rd := rd) (wr := wr) (hpre _ h3.ent) hc3 hw3
    fun s₄ rd4 wr4 hcs4 hf4 _ hpost4 _ => ?_)
  obtain ⟨s₂, hm2, hg2, hk2⟩ := hpost4
  have s4sp : s₄.gpr .rsp = S - BitVec.ofNat 64 16 := by rw [hcs4 .rsp (by decide), sp3]
  have s4bx : s₄.gpr .rbx = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [hcs4 .rbx (by decide), h3.rbx]
  refine WP.mono (epi_ok (s := s₄) (by rw [wr4, w3]; exact List.mem_cons_self) (by rw [s4sp]; exact c0) s4bx)
    fun s₅ ⟨hmx5, hm5, hg5, hrd5, hwr5⟩ => ⟨?_, ?_, ?_⟩
  · rw [hg5, s4sp, s1sp]
  · rw [hwr5, wr4, w3, s1wr]
  have s5sp : s₅.gpr .rsp = S - BitVec.ofNat 64 16 := by rw [hg5, s4sp]
  rw [s4sp] at hm5
  have f5' : Frame [⟨S - BitVec.ofNat 64 16, 4⟩] s₄.mem s₅.mem := by
    rw [hm5]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have s16 : Region.Sub ⟨S - BitVec.ofNat 64 16, 4⟩ (below S 16) := Region.sub_prefix (by omega)
  have f5 : Frame [below S 16] s₄.mem s₅.mem :=
    f5'.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton] at hr; subst hr; exact s16⟩
  -- The caller's `rbx`, from the frame's first push, which nothing overwrites.
  have hd8 : ∀ r ∈ wr ++ [below (s₃.gpr .rsp) (8 * (c.depth + 1))], Region.Disjoint ⟨S - 8, 8⟩ r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (hdj r hr).sub_left (show Region.Sub (below S 8) (below S 16) from below_sub (by omega) (by omega))
    · rw [List.mem_singleton] at hr; subst hr
      rw [sp3]
      show Region.Disjoint _ ⟨S - BitVec.ofNat 64 16 - BitVec.ofNat 64 (8 * (c.depth + 1)), 8 * (c.depth + 1)⟩
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact disj S (a := 8) (n := 8) (b := 16 + 8 * (c.depth + 1)) (m := 8 * (c.depth + 1)) (by omega)
        (by omega) (by omega)
  have hbx5 : s₅.mem.readW (S - 8) 64 = s.gpr .rbx := by
    rw [f5'.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact disj S (a := 8) (n := 8) (b := 16) (m := 4) (by omega) (by omega) (by omega)) (by decide),
      hf4.readW (Region.contains_self _ _) hd8 (by decide), sv3]
  refine hQ _ ?_ ?_ ?_ ?_ ⟨s₃.callEntry, s₂, h3.ent, ?_, fun r h1 h2 => ?_, hk2⟩ ?_
  · rw [popped_rd, hrd5, rd4, r3]
  · rw [popped_wr, hwr5, wr4, w3]; rfl
  · intro r hr
    by_cases h1 : r = .rsp
    · subst h1; rw [popped_rsp, s5sp, hSdef]; simp only [List.length_cons, List.length_nil]; bv_omega
    by_cases h2 : r = .rbx
    · subst h2
      show (popReg s₅ .rbx 2).gpr .rbx = _
      rw [popReg2, s5sp, e8, hbx5]
    · rw [popped_gpr _ _ _ h1 h2, hg5, hcs4 r hr, h3.gpr r h1 (by rintro rfl; simp [calleeSaved] at hr) h2]
  · rw [popped_mem]
    refine ((m3.sub fun r hr => ⟨below S (8 * c.depth + 24), by simp, ?_⟩).trans (hf4.sub fun r hr => ?_)).trans
      (f5.sub fun r hr => ⟨below S (8 * c.depth + 24), by simp, ?_⟩)
    · rw [List.mem_singleton] at hr; subst hr; exact below_sub (by omega) (by omega)
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        refine ⟨below S (8 * c.depth + 24), by simp, ?_⟩
        rw [sp3]; exact sub_below S (by omega) (by omega)
    · rw [List.mem_singleton] at hr; subst hr; exact below_sub (by omega) (by omega)
  · rw [popped_mem, hm2]; exact f5
  · rw [popped_gpr _ _ _ h1 h2, hg2 r h1, hg5]
  · rw [popped_mxcsr, hmx5]

/-- Two runs of `mcdtCall n c`, from states with the same stack pointer, from each of which `c`
runs as its contract says (narrowed in each run to regions of its own), and whose states at the
entry of `c` are related by its contract's public relation, leak the same trace. -/
theorem RelCT.mcdtCall {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp ∧ 8 * c.depth + 24 ≤ (s₁.gpr .rsp).toNat ∧
      ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
        Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
        Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr ∧
        ∀ e₁ e₂, EntryOf s₁ e₁ → EntryOf s₂ e₂ → k.pre (e₁.withRegions rd₁ wr₁) ∧
          k.pre (e₂.withRegions rd₂ wr₂) ∧ k.pub (e₁.withRegions rd₁ wr₁) (e₂.withRegions rd₂ wr₂)) :
    RelCT isa P (mcdtCall n c) fun _ _ => True := by
  unfold VG.Impl.Mcdt.X86_64.mcdtCall
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ h => (hP _ _ h).1) ?_
  -- The prologue: its addresses are `rsp`'s.
  refine RelCT.seq (R := fun (x y : State) => ∃ s₁ s₂, P s₁ s₂ ∧ Pro s₁ x ∧ Pro s₂ y) ?_ ?_
  · intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, ha, hb⟩ e₁ e₂
    obtain ⟨hsp₁, hS, -⟩ := hP _ _ hp
    refine ⟨(taintRel (P := fun x y => x.gpr .rsp = y.gpr .rsp) [.rsp] (fun x y h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact h)
      (by taint_decide)) _ _ _ _ _ _ (by show a.gpr .rsp = b.gpr .rsp; rw [ha, hb, pushed_rsp, pushed_rsp, hsp₁]) e₁ e₂ |>.1, s₁, s₂, hp, ?_, ?_⟩
    · obtain ⟨_, u, f, g⟩ := pro_run (s := s₁) (by omega)
      rw [ha] at e₁; obtain ⟨-, rfl⟩ := Exec.det e₁ f; exact g
    · obtain ⟨_, u, f, g⟩ := pro_run (s := s₂) (by rw [← hsp₁]; omega)
      rw [hb] at e₂; obtain ⟨-, rfl⟩ := Exec.det e₂ f; exact g
  refine RelCT.seq (R := fun (x y : State) => ∃ s₁ s₂, P s₁ s₂ ∧ x.gpr .rsp = s₁.gpr .rsp - BitVec.ofNat 64 16 ∧
    y.gpr .rsp = s₂.gpr .rsp - BitVec.ofNat 64 16) ?_ ?_
  · -- The call, as `RelCT.callEx` relates it.
    have hcall : ∀ x y, (∃ s₁ s₂, P s₁ s₂ ∧ Pro s₁ x ∧ Pro s₂ y) → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
        k.pre (x.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y.callEntry.withRegions rd₂ wr₂) ∧
        k.pub (x.callEntry.withRegions rd₁ wr₁) (y.callEntry.withRegions rd₂ wr₂) ∧
        Covers (rd₁ ++ wr₁) (x.rd ++ x.wr) ∧ Covers wr₁ x.wr ∧
        Covers (rd₂ ++ wr₂) (y.rd ++ y.wr) ∧ Covers wr₂ y.wr ∧ x.gpr .rsp = y.gpr .rsp := by
      intro x y ⟨s₁, s₂, hp, h₁, h₂⟩
      obtain ⟨hsp₁, -, rd₁, wr₁, rd₂, wr₂, c₁, w₁, c₂, w₂, hk⟩ := hP _ _ hp
      obtain ⟨p₁, p₂, hpub⟩ := hk _ _ h₁.ent h₂.ent
      obtain ⟨c₁', w₁'⟩ := covers_frame ⟨s₁.gpr .rsp - BitVec.ofNat 64 16, 16⟩ c₁ w₁
      obtain ⟨c₂', w₂'⟩ := covers_frame ⟨s₂.gpr .rsp - BitVec.ofNat 64 16, 16⟩ c₂ w₂
      refine ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h₁.rd, h₁.wr]; exact c₁'
      · rw [h₁.wr]; exact w₁'
      · rw [h₂.rd, h₂.wr]; exact c₂'
      · rw [h₂.wr]; exact w₂'
      · rw [h₁.rsp, h₂.rsp, hsp₁]
    intro x y t₁ t₂ x' y' hr e₁ e₂
    refine ⟨(RelCT.callEx hv hct hcall) _ _ _ _ _ _ hr e₁ e₂ |>.1, ?_⟩
    obtain ⟨s₁, s₂, hp, h₁, h₂⟩ := hr
    obtain ⟨-, hS, -⟩ := hP _ _ hp
    obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, -, c₁, w₁, c₂, w₂, -⟩ := hcall x y ⟨s₁, s₂, hp, h₁, h₂⟩
    have hd : 8 * c.depth + 16 < 2 ^ 64 := by have := (s₁.gpr .rsp).isLt; omega
    obtain ⟨_, u₁, f₁, g₁⟩ := WP.call_mx (Q := fun u => u.gpr .rsp = x.gpr .rsp) hv hsp hd p₁ c₁ w₁
      fun u _ _ hcs _ _ _ _ => hcs .rsp (by decide)
    obtain ⟨_, u₂, f₂, g₂⟩ := WP.call_mx (Q := fun u => u.gpr .rsp = y.gpr .rsp) hv hsp hd p₂ c₂ w₂
      fun u _ _ hcs _ _ _ _ => hcs .rsp (by decide)
    obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
    exact ⟨s₁, s₂, hp, by rw [g₁, h₁.rsp], by rw [g₂, h₂.rsp]⟩
  · -- The epilogue: its addresses are `rsp`'s.
    exact taintRel [.rsp] (fun x y ⟨s₁, s₂, hp, h₁, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁, h₂, (hP _ _ hp).1]) (by taint_decide)

end VG.Proof.Mcdt.X86_64
