module

public import VerifiedGarbage.Impl.Xdh.X86_64
public import VerifiedGarbage.Proof.Xdh.Common
public import VerifiedGarbage.Proof.Xdh.Rel
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Xdh.X86_64
meta import VerifiedGarbage.Proof.Xdh.Common
meta import VerifiedGarbage.Proof.Xdh.Rel
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 and X448 exchange, with RFC 7748's check, on x86-64

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Xdh/RISCV64.lean`): for any callee `c` that never writes `rsp`,
whose calls nest at most one deep, and whose contract `k` its proof gives
(`Callee`), `Impl.Xdh.X86_64.exchange` pushes `out` at `E - 8` (`E` the stack
pointer on entry), calls `c` with its arguments as they came (`called_wp`),
which writes neither, pops `out` into `rdx` (`Popped`), ORs the `n` bytes
there into `rcx` (`orBytes_wp`) and returns the result in `rax`
(`checked_wp`). Its frame, its call and the callee's calls use the 24 bytes
below `E`. Two runs whose pointers agree (`Pub`) leak the same trace
(`exchange_ct`).
-/

@[expose] public section

namespace VG.Proof.Xdh.X86_64

open VG VG.X86_64 VG.Impl.Xdh.X86_64
open VG.Spec.X25519 (bytesAt)
open VG.Proof.Xdh (Eq2 TT rel_seq ct_of)

/-! ## Steps -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_or {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xori {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_)
  · simp [reduceExec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl, rfl⟩

theorem wp_movzx8 {d b : Reg} {o : Nat} {a : Addr} (ha : s.gpr b + BitVec.ofNat 64 o = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, none, 1, (o : Int)⟩ :: is)) s Q := by
  have e : s.ea ⟨b, none, 1, (o : Int)⟩ = a := by
    rw [← ha]; simp [State.ea]
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [reduceExec, State.load8, e, hin]

end

section
variable (n w : Nat) (s : State)

/-- The regions of the arguments, of the return address and of the `S` bytes
below it. -/
abbrev outR : Region := ⟨s.gpr .rdi, n⟩
abbrev scR : Region := ⟨s.gpr .rsi, n⟩
abbrev ptR : Region := ⟨s.gpr .rdx, n⟩
abbrev wsR : Region := ⟨s.gpr .rcx, w⟩
abbrev retR : Region := ⟨s.gpr .rsp, 8⟩
abbrev stkR (S : Nat) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 S, S⟩

end

/-- What a function with the signature of `vg_x25519` (`n`-byte buffers, `w`
bytes of working space), whose calls and frames use `S` bytes of stack,
needs at its entry. -/
def Pre (n w S : Nat) (s : State) : Prop :=
  s.rd = [scR n s, ptR n s] ∧ s.wr = [outR n s, wsR w s] ∧
    (outR n s).Disjoint (scR n s) ∧ (outR n s).Disjoint (ptR n s) ∧ (outR n s).Disjoint (wsR w s) ∧
    (scR n s).Disjoint (wsR w s) ∧ (ptR n s).Disjoint (wsR w s) ∧
    (retR s).Disjoint (outR n s) ∧ (retR s).Disjoint (scR n s) ∧ (retR s).Disjoint (ptR n s) ∧
    (retR s).Disjoint (wsR w s) ∧
    (stkR s S).Disjoint (outR n s) ∧ (stkR s S).Disjoint (scR n s) ∧ (stkR s S).Disjoint (ptR n s) ∧
    (stkR s S).Disjoint (wsR w s) ∧
    (s.gpr .rdi).toNat + n ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + n ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + n ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + w ≤ 2 ^ 64 ∧ S ≤ (s.gpr .rsp).toNat

theorem Pre.stk {n w S : Nat} {s : State} (h : Pre n w S s) : S ≤ (s.gpr .rsp).toNat :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- What it leaves: `f` of the scalar and the point at `out`, and 0 in the
low word of `rax` if that is all zero, 1 otherwise. -/
def ExPost (n : Nat) (f : List Byte → List Byte → List Byte) (s s' : State) : Prop :=
  bytesAt s'.mem (s.gpr .rdi) n = f (bytesAt s.mem (s.gpr .rsi) n) (bytesAt s.mem (s.gpr .rdx) n) ∧
    (s'.gpr .rax).setWidth 32 =
      if f (bytesAt s.mem (s.gpr .rsi) n) (bytesAt s.mem (s.gpr .rdx) n) = List.replicate n 0 then 0 else 1

/-- What two runs agree on: the pointers. -/
def Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- The exchange function's contract on x86-64. -/
def exContract (n w : Nat) (f : List Byte → List Byte → List Byte) : Contract isa where
  pre := Pre n w 24
  post := ExPost n f
  pub := Pub

/-- The callee, by its contract `k`. -/
structure Callee (n w : Nat) (f : List Byte → List Byte → List Byte) (c : Prog isa) (k : Contract isa) :
    Prop where
  hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  hct : ConstantTime isa k.pre k.pub c
  pre : ∀ s, Pre n w 8 s → k.pre s
  post : ∀ s s', k.post s s' →
    bytesAt s'.mem (s.gpr .rdi) n = f (bytesAt s.mem (s.gpr .rsi) n) (bytesAt s.mem (s.gpr .rdx) n)
  pub : ∀ s₁ s₂, Pub s₁ s₂ → k.pub s₁ s₂
  noSp : NoSp c
  depth : c.depth ≤ 1

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' := Covers.of_mem h

/-- No instruction of `c` writes `rsp` if its inlining is checked (`Code.InlineOk`). -/
theorem NoSp.of_inlineOk {c : Prog isa} (h : c.InlineOk = true) : NoSp c := by
  have h' : c.inline.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    intro i hi; simp [Code.clobbers_rsp_of_inlineOk h i hi]
  rw [Code.allInstrs_inline, Code.allInstrs_eq] at h'
  intro i hi; simpa using List.all_eq_true.mp h' i hi

/-! ## Regions by their bounds -/

theorem sub_of_toNat {r R : Region} (h1 : R.base.toNat ≤ r.base.toNat)
    (h2 : r.base.toNat + r.len ≤ R.base.toNat + R.len) (h3 : R.base.toNat + R.len ≤ 2 ^ 64) : r.Sub R := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have e : x - R.base = (x - r.base) + (r.base - R.base) := by bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h1)]
  rw [Nat.mod_eq_of_lt (by have := r.base.isLt; omega)]
  omega

theorem contains_of_toNat {R : Region} {a : Addr} {k : Nat} (h1 : R.base.toNat ≤ a.toNat)
    (h2 : a.toNat + k ≤ R.base.toNat + R.len) : R.Contains a k := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h1)]
  omega

theorem sub_toNat' {a : Addr} {k : Nat} (h : k ≤ a.toNat) : (a - BitVec.ofNat 64 k).toNat = a.toNat - k :=
  toNat_sub_ofNat h

section
variable {n w : Nat} {s : State}

theorem stk_toNat (h : Pre n w 24 s) : (stkR s 24).base.toNat = (s.gpr .rsp).toNat - 24 :=
  sub_toNat' h.stk

/-- A region of the 24 bytes below `E`, by its bounds. -/
theorem in_stk (h : Pre n w 24 s) {r : Region} (h1 : (s.gpr .rsp).toNat - 24 ≤ r.base.toNat)
    (h2 : r.base.toNat + r.len ≤ (s.gpr .rsp).toNat) : r.Sub (stkR s 24) := by
  have := h.stk
  have := (s.gpr .rsp).isLt
  refine sub_of_toNat (by rw [stk_toNat h]; exact h1) (by rw [stk_toNat h]; show _ ≤ _ - 24 + 24; omega)
    (by rw [stk_toNat h]; show _ - 24 + 24 ≤ _; omega)

theorem slot_toNat (h : Pre n w 24 s) : (s.gpr .rsp - BitVec.ofNat 64 8).toNat = (s.gpr .rsp).toNat - 8 :=
  sub_toNat' (by have := h.stk; omega)

end

/-! ## The call -/

/-- The memory once `out` is pushed. -/
abbrev pMem (s : State) : Mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr .rdi)

theorem pushed_mem (s : State) : (pushed [.rdi] s).mem = pMem s := rfl

theorem pushed_rsp' (s : State) : (pushed [.rdi] s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8 :=
  pushed_rsp _ _

/-- The callee's entry, with the regions it is given. -/
abbrev cEntry (s : State) : State := (pushed [.rdi] s).callEntry.withRegions s.rd s.wr

theorem cEntry_gpr (s : State) {r : Reg} (h : r ≠ .rsp) : (cEntry s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]

theorem cEntry_rsp {n w : Nat} {s : State} (h : Pre n w 24 s) :
    ((cEntry s).gpr .rsp).toNat = (s.gpr .rsp).toNat - 16 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, pushed_rsp', show (8 : Addr) = BitVec.ofNat 64 8 from rfl,
    sub_toNat' (by rw [slot_toNat h]; have := h.stk; omega), slot_toNat h]
  omega

theorem cEntry_pre {n w : Nat} {s : State} (h : Pre n w 24 s) : Pre n w 8 (cEntry s) := by
  have hstk := h.stk
  have hE := cEntry_rsp h
  obtain ⟨rd, wr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, b0, b1, b2, b3, -⟩ := h
  have h' : Pre n w 24 s := ⟨rd, wr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, b0, b1, b2, b3, hstk⟩
  have g0 := cEntry_gpr s (r := .rdi) (by decide)
  have g1 := cEntry_gpr s (r := .rsi) (by decide)
  have g2 := cEntry_gpr s (r := .rdx) (by decide)
  have g3 := cEntry_gpr s (r := .rcx) (by decide)
  have eO : outR n (cEntry s) = outR n s := by rw [outR, g0]
  have eS : scR n (cEntry s) = scR n s := by rw [scR, g1]
  have eP : ptR n (cEntry s) = ptR n s := by rw [ptR, g2]
  have eW : wsR w (cEntry s) = wsR w s := by rw [wsR, g3]
  have hK : ((cEntry s).gpr .rsp - BitVec.ofNat 64 8).toNat = (s.gpr .rsp).toNat - 24 := by
    rw [sub_toNat' (by rw [hE]; omega), hE]; omega
  have sR : (retR (cEntry s)).Sub (stkR s 24) :=
    in_stk h' (show _ ≤ ((cEntry s).gpr .rsp).toNat by rw [hE]; omega)
      (show ((cEntry s).gpr .rsp).toNat + 8 ≤ _ by rw [hE]; omega)
  have sK : (stkR (cEntry s) 8).Sub (stkR s 24) :=
    in_stk h' (show _ ≤ ((cEntry s).gpr .rsp - BitVec.ofNat 64 8).toNat by rw [hK])
      (show ((cEntry s).gpr .rsp - BitVec.ofNat 64 8).toNat + 8 ≤ _ by rw [hK]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eS, eP]; exact rd
  · rw [eO, eW]; exact wr
  · rw [eO, eS]; exact d1
  · rw [eO, eP]; exact d2
  · rw [eO, eW]; exact d3
  · rw [eS, eW]; exact d4
  · rw [eP, eW]; exact d5
  · rw [eO]; exact k1.sub_left sR
  · rw [eS]; exact k2.sub_left sR
  · rw [eP]; exact k3.sub_left sR
  · rw [eW]; exact k4.sub_left sR
  · rw [eO]; exact k1.sub_left sK
  · rw [eS]; exact k2.sub_left sK
  · rw [eP]; exact k3.sub_left sK
  · rw [eW]; exact k4.sub_left sK
  · rw [g0]; exact b0
  · rw [g1]; exact b1
  · rw [g2]; exact b2
  · rw [g3]; exact b3
  · rw [hE]; omega

theorem bytes_keep {R : Region} {m m' : Mem} (hf : Frame [R] m m') {p : Addr} {k : Nat}
    (hd : R.Disjoint ⟨p, k⟩) (hn : p.toNat + k ≤ 2 ^ 64) : bytesAt m' p k = bytesAt m p k := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact hd _ hc (Offset.contains_base _ (by omega) (by omega))

/-- After the call: `f` of the arguments at `out`, and the frame and the return address as they were. -/
structure Called (n : Nat) (f : List Byte → List Byte → List Byte) (s z : State) : Prop where
  out : bytesAt z.mem (s.gpr .rdi) n = f (bytesAt s.mem (s.gpr .rsi) n) (bytesAt s.mem (s.gpr .rdx) n)
  slot : z.mem.readW (s.gpr .rsp - BitVec.ofNat 64 8) 64 = s.gpr .rdi
  ret : z.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
  saved : ∀ r ∈ calleeSaved, r ≠ .rsp → z.gpr r = s.gpr r
  rsp : z.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8
  rd : z.rd = s.rd
  wr : z.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩ :: s.wr
  mxcsr : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem called_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} {s : State} (h : Pre n w 24 s) :
    WP isa (.call name c) (pushed [.rdi] s) (Called n f s) := by
  have hstk := h.stk
  have hcp := cEntry_pre h
  have hS := slot_toNat h
  have hdep := hk.depth
  obtain ⟨rd, wr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, b0, b1, b2, b3, -⟩ := h
  have h' : Pre n w 24 s := ⟨rd, wr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, b0, b1, b2, b3, hstk⟩
  have hcov : Covers (s.rd ++ s.wr) ((pushed [.rdi] s).rd ++ (pushed [.rdi] s).wr) := covers_mem fun r hr => by
    rw [pushed_rd, pushed_wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hw : Covers s.wr (pushed [.rdi] s).wr := covers_mem fun r hr => by
    rw [pushed_wr]; exact List.mem_cons_of_mem _ hr
  refine WP.call_mx hk.hv hk.noSp (by omega) (hk.pre _ hcp) hcov hw
    fun z rd' wr' cs' fr' _ ⟨s₂, m₂, _, post₂⟩ mx' => ?_
  have hpost := hk.post _ _ post₂
  rw [m₂, cEntry_gpr s (by decide), cEntry_gpr s (by decide), cEntry_gpr s (by decide)] at hpost
  -- The push and the return address left the scalar and the point.
  have sP : (⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩ : Region).Sub (stkR s 24) :=
    in_stk h' (show _ ≤ (s.gpr .rsp - BitVec.ofNat 64 8).toNat by rw [hS]; omega)
      (show (s.gpr .rsp - BitVec.ofNat 64 8).toNat + 8 ≤ _ by rw [hS]; omega)
  have hE := cEntry_rsp h'
  have fc : Frame [stkR s 24] s.mem (cEntry s).mem := by
    show Frame _ s.mem (pushed [.rdi] s).callEntry.mem
    rw [State.callEntry_mem, pushed_mem, pushed_rsp']
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_of_toNat ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (contains_of_toNat ?_ ?_)
    · rw [stk_toNat h', show (8 : Addr) = BitVec.ofNat 64 8 from rfl, hS]; omega
    · show (s.gpr .rsp - 8).toNat + 64 / 8 ≤ (stkR s 24).base.toNat + 24
      rw [stk_toNat h', show (8 : Addr) = BitVec.ofNat 64 8 from rfl, hS]; omega
    · have := hE; simp only [State.withRegions_gpr, State.callEntry_rsp, pushed_rsp'] at this
      rw [stk_toNat h', this]; omega
    · have := hE; simp only [State.withRegions_gpr, State.callEntry_rsp, pushed_rsp'] at this
      show (s.gpr .rsp - BitVec.ofNat 64 8 - 8).toNat + 64 / 8 ≤ (stkR s 24).base.toNat + 24
      rw [stk_toNat h', this]; omega
  rw [bytes_keep fc k2 b1, bytes_keep fc k3 b2] at hpost
  -- The stack the call used.
  have sB : (below ((pushed [.rdi] s).gpr .rsp) (8 * (c.depth + 1))).Sub (stkR s 24) := by
    have e₁ : (below ((pushed [.rdi] s).gpr .rsp) (8 * (c.depth + 1))).base.toNat =
        (s.gpr .rsp).toNat - 8 - 8 * (c.depth + 1) := by
      show ((pushed [.rdi] s).gpr .rsp - BitVec.ofNat 64 (8 * (c.depth + 1))).toNat = _
      rw [pushed_rsp', sub_toNat' (by rw [hS]; omega), hS]
    exact in_stk h' (by rw [e₁]; omega) (by rw [e₁]; show _ + 8 * (c.depth + 1) ≤ _; omega)
  have slotB : (⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint
      (below ((pushed [.rdi] s).gpr .rsp) (8 * (c.depth + 1))) := by
    refine Offset.disjoint_of_le (r₁ := below _ _) (r₂ := ⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩) ?_ ?_ |>.symm
    · show ((pushed [.rdi] s).gpr .rsp - BitVec.ofNat 64 (8 * (c.depth + 1))).toNat + 8 * (c.depth + 1) ≤
        (s.gpr .rsp - BitVec.ofNat 64 8).toNat
      rw [pushed_rsp', sub_toNat' (by rw [hS]; omega), hS]; omega
    · show (s.gpr .rsp - BitVec.ofNat 64 8).toNat + 8 ≤ 2 ^ 64
      rw [hS]; have := (s.gpr .rsp).isLt; omega
  have retB : (retR s).Disjoint (stkR s 24) := Offset.base_disjoint_below _ (by decide)
  have fp : Frame [stkR s 24] s.mem (pushed [.rdi] s).mem := by
    rw [pushed_mem]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_of_toNat ?_ ?_)
    · rw [stk_toNat h', show (8 : Addr) = BitVec.ofNat 64 8 from rfl, hS]; omega
    · show (s.gpr .rsp - 8).toNat + 64 / 8 ≤ (stkR s 24).base.toNat + 24
      rw [stk_toNat h', show (8 : Addr) = BitVec.ofNat 64 8 from rfl, hS]; omega
  have keep {R : Region} (hR : R.Disjoint (stkR s 24)) (ho : R.Disjoint (outR n s))
      (hw' : R.Disjoint (wsR w s)) {a : Addr} (ha : R.Contains a 8) :
      z.mem.readW a 64 = s.mem.readW a 64 := by
    rw [Frame.readW fr' ha (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rw [wr] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ho
        · exact hw'
      · rw [List.mem_singleton.mp hr]; exact hR.sub_right sB) (by decide)]
    exact Frame.readW fp ha (fun r hr => by rw [List.mem_singleton.mp hr]; exact hR) (by decide)
  refine ⟨hpost, ?_, keep retB r1 r4 (Region.contains_self _ _), fun r hr hr' => ?_, ?_, rd'.trans (pushed_rd _ _),
    wr'.trans (pushed_wr _ _), ?_⟩
  · rw [Frame.readW fr' (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rw [wr] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact k1.sub_left sP
        · exact k4.sub_left sP
      · rw [List.mem_singleton.mp hr]; exact slotB) (by decide), pushed_mem]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [cs' r hr, pushed_gpr _ _ hr']
  · rw [cs' .rsp (by simp [calleeSaved]), pushed_rsp']
  · rw [mx', pushed_mxcsr]

/-- After the pop of `out` into `rdx`. -/
structure Popped (n : Nat) (f : List Byte → List Byte → List Byte) (s u : State) : Prop where
  out : bytesAt u.mem (s.gpr .rdi) n = f (bytesAt s.mem (s.gpr .rsi) n) (bytesAt s.mem (s.gpr .rdx) n)
  ret : u.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
  saved : ∀ r ∈ calleeSaved, u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mxcsr : u.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  rdx : u.gpr .rdx = s.gpr .rdi

theorem popped_of {n : Nat} {f : List Byte → List Byte → List Byte} {s z : State} (hz : Called n f s z) :
    Popped n f s (popped .rdx 1 z) := by
  refine ⟨by rw [popped_mem]; exact hz.out, by rw [popped_mem]; exact hz.ret, fun r hr => ?_, by
    rw [popped_rd, hz.rd], by rw [popped_wr, hz.wr]; rfl, by rw [popped_mxcsr]; exact hz.mxcsr, ?_⟩
  · by_cases h : r = .rsp
    · subst h; rw [popped_rsp, hz.rsp]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ h (by rintro rfl; simp [calleeSaved] at hr), hz.saved r hr h]
  · show (popReg z .rdx 1).gpr .rdx = _
    simp only [popReg, State.setReg, show Reg.rdx ≠ Reg.rsp by decide, ↓reduceIte]
    rw [hz.rsp]; exact hz.slot

/-! ## The check -/

theorem orBytes_wp (a : Addr) (m : Mem) : ∀ (i : Nat), i < 2 ^ 31 → ∀ (u : State) (is : List Instr)
    (Q : State → Prop), u.gpr .rdx = a → u.mem = m →
    (∀ j < i, InRegions (u.rd ++ u.wr) (a + BitVec.ofNat 64 j) 1) →
    (∀ u', u'.gpr .rcx = u.gpr .rcx ||| (orAll m a i).setWidth 64 → u'.gpr .rdx = a → u'.mem = m →
      u'.rd = u.rd → u'.wr = u.wr → u'.mxcsr = u.mxcsr →
      (∀ r, r ≠ .rcx → r ≠ .rax → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) →
    WP isa (.block (orBytes i ++ is)) u Q := by
  intro i
  induction i with
  | zero =>
    intro _ u is Q ht hm _ k
    exact k u (by simp [orAll]) ht hm rfl rfl rfl fun _ _ _ => rfl
  | succ i ih =>
    intro hi u is Q ht hm hin k
    rw [orBytes, List.append_assoc]
    refine ih (by omega) u _ Q ht hm (fun j hj => hin j (by omega)) fun u' g1 g0 gm grd gwr gx go => ?_
    refine wp_movzx8 (a := a + BitVec.ofNat 64 i) (by rw [g0]) (by rw [grd, gwr]; exact hin i (by omega))
      fun u₁ v₁ => ?_
    refine wp_or fun u₂ v₂ => ?_
    refine k u₂ ?_ ?_ ?_ ?_ ?_ ?_ fun r h1 h2 => ?_
    · rw [v₂.gpr, v₁.other _ (by decide), v₁.gpr, g1, gm, orAll, BitVec.setWidth_or, BitVec.or_assoc]
    · rw [v₂.other _ (by decide), v₁.other _ (by decide), g0]
    · rw [v₂.mem, v₁.mem, gm]
    · rw [v₂.rd, v₁.rd, grd]
    · rw [v₂.wr, v₁.wr, gwr]
    · rw [v₂.mxcsr, v₁.mxcsr, gx]
    · rw [v₂.other r h1, v₁.other r h2, go r h1 h2]

/-- After the check. -/
structure Checked (n : Nat) (f : List Byte → List Byte → List Byte) (s v : State) : Prop where
  popped : Popped n f s v
  rax : (v.gpr .rax).setWidth 32 = if orAll v.mem (s.gpr .rdi) n = 0 then 0 else 1

theorem checked_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {s u : State} (h : Pre n w 24 s)
    (hn : n < 2 ^ 31) (hu : Popped n f s u) : WP isa (.block (check n)) u (Checked n f s) := by
  obtain ⟨rd, wr, -, -, -, -, -, -, -, -, -, -, -, -, -, b0, -, -, -, -⟩ := h
  unfold check
  refine wp_movi fun u₁ v₁ => ?_
  refine orBytes_wp (s.gpr .rdi) u.mem n hn u₁ _ _ (by rw [v₁.other _ (by decide), hu.rdx]) v₁.mem
    (fun j hj => ⟨outR n s, by rw [v₁.rd, v₁.wr, hu.rd, hu.wr, wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩) fun y g1 _ gm grd gwr gx go => ?_
  refine wp_subi fun u₂ v₂ => wp_shr (by decide) fun u₃ v₃ => wp_xori fun u₄ v₄ =>
    wp_mov fun u₅ v₅ => WP.block_nil ?_
  have hm : u₅.mem = u.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, gm]
  refine ⟨⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hu.out
  · rw [hm]; exact hu.ret
  · have h1 : r ≠ .rax := by rintro rfl; simp [calleeSaved] at hr
    have h2 : r ≠ .rcx := by rintro rfl; simp [calleeSaved] at hr
    rw [v₅.other r h1, v₄.other r h2, v₃.other r h2, v₂.other r h2, go r h2 h1, v₁.other r h2]
    exact hu.saved r hr
  · rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, grd, v₁.rd, hu.rd]
  · rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, gwr, v₁.wr, hu.wr]
  · rw [v₅.mxcsr, v₄.mxcsr, v₃.mxcsr, v₂.mxcsr, gx, v₁.mxcsr]; exact hu.mxcsr
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      go _ (by decide) (by decide), v₁.other _ (by decide), hu.rdx]
  · rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, g1, v₁.gpr, hm,
      show (0 : BitVec 32).signExtend 64 = 0 from rfl, show (1 : BitVec 32).signExtend 64 = 1 from rfl,
      show ∀ x : BitVec 64, 0 ||| x = x from fun x => BitVec.zero_or]
    exact result_shr _

/-! ## The whole function -/

theorem frame_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} {s : State} (h : Pre n w 24 s) :
    WP isa (.frame (.push [.rdi]) (.call name c) (.pop .rdx 1)) s (Popped n f s) := by
  have hstk := h.stk
  refine WP.frame (by simp) (by decide) (by decide) (by simp only [List.length_singleton]; omega) ?_
  exact WP.mono (called_wp hk h) fun z hz =>
    ⟨by rw [hz.rsp, pushed_rsp'], by rw [hz.wr, pushed_wr]; rfl, popped_of hz⟩

theorem exchange_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 2 ^ 31) {s : State} (h : Pre n w 24 s) :
    WP isa (exchange name c n) s fun z => abiPreserved s z ∧ ExPost n f s z := by
  refine WP.seq (WP.mono (frame_wp hk h) fun u hu => ?_)
  refine WP.mono (checked_wp h hn hu) fun v hv => ?_
  refine ⟨⟨hv.popped.saved, hv.popped.ret, hv.popped.mxcsr⟩, hv.popped.out, ?_⟩
  rw [hv.rax]
  exact result_spec _ _ _ _ hv.popped.out

/-! ## Constant time -/

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact Taint.agree_ofRegs hr) h

theorem exchange_ct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String}
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.rdx]) (.block (check n)) hc).isSome = true) :
    ConstantTime isa (Pre n w 24) Pub (exchange name c n) := by
  obtain ⟨_, ht⟩ := ht
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨qsp, q0, q1, q2, q3⟩ := hq
  have hrd : σ₂.rd = σ₁.rd := by rw [p₁.1, p₂.1]; simp only [scR, ptR, q1, q2]
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.2.1, p₂.2.1]; simp only [outR, wsR, q0, q3]
  refine rel_seq ?_ (frame_wp hk p₁) (frame_wp hk p₂) fun u₁ u₂ hu₁ hu₂ => ?_
  · refine (RelCT.frame (P := Eq2 σ₁ σ₂) (R := TT (M := isa)) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp)
      ((?_ : RelCT isa (Eq2 (pushed [.rdi] σ₁) (pushed [.rdi] σ₂)) _ (TT (M := isa))).mono
        (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
    refine RelCT.call hk.hv hk.hct σ₁.rd σ₁.wr fun a b ⟨ha, hb⟩ => ?_
    subst ha hb
    have c₂ := cEntry_pre p₂
    rw [cEntry, hrd, hwr] at c₂
    have hcov (s : State) (hrd' : s.rd = σ₁.rd) (hwr' : s.wr = σ₁.wr) :
        Covers (σ₁.rd ++ σ₁.wr) ((pushed [.rdi] s).rd ++ (pushed [.rdi] s).wr) ∧
          Covers σ₁.wr (pushed [.rdi] s).wr :=
      ⟨covers_mem fun r hr => by
        rw [pushed_rd, pushed_wr, hrd', hwr']
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr),
       covers_mem fun r hr => by rw [pushed_wr, hwr']; exact List.mem_cons_of_mem _ hr⟩
    refine ⟨hk.pre _ (cEntry_pre p₁), hk.pre _ c₂, hk.pub _ _ ?_, (hcov σ₁ rfl rfl).1, (hcov σ₁ rfl rfl).2,
      (hcov σ₂ hrd hwr).1, (hcov σ₂ hrd hwr).2, by rw [pushed_rsp', pushed_rsp', qsp]⟩
    have g {s : State} (r : Reg) (hr : r ≠ .rsp) :
        ((pushed [.rdi] s).callEntry.withRegions σ₁.rd σ₁.wr).gpr r = s.gpr r := by
      rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_gpr, State.callEntry_rsp, pushed_rsp', qsp]
    · rw [g _ (by decide), g _ (by decide), q0]
    · rw [g _ (by decide), g _ (by decide), q1]
    · rw [g _ (by decide), g _ (by decide), q2]
    · rw [g _ (by decide), g _ (by decide), q3]
  · exact rel_taint [.rdx] (by simp [hu₁.rdx, hu₂.rdx, q0]) ht

/-! ## `Verified` -/

theorem exchange_correct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 2 ^ 31) :
    ∀ s, (exContract n w f).pre s →
      ∃ t s', Exec isa (exchange name c n) s t s' ∧ abiPreserved s s' ∧ (exContract n w f).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := exchange_wp hk (name := name) hn h
    exact ⟨t, s', he, ha, hp⟩

end VG.Proof.Xdh.X86_64
