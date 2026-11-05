module

public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.TCB.X86_64.Residue
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# Returning without secret residue (x86-64)

`Verified.scrub`: code verified against a contract that `Sig.contract`
derives, whose frames and calls use at most the contract's `stack` bytes,
followed by `Impl.Scrub.X86_64.scrubTail` (`scrub`), is verified against the
same contract and returns without secret residue (`NoResidue`). The proof of
the code is used as it is: what `scrub` adds is checked once, here, for all
code (`tail_run`): it zeroes the stack below `rsp` (`wipe_run`), the SSE
registers and the caller-saved general-purpose registers, and its trace
depends only on `rsp`. What the code itself must satisfy is decidable
(`SpSafe`, its depth, the level of its vector instructions,
`ResidueKeep.lean`), but for its postcondition, which must read the memory
on return only within the buffers (`hpost`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- The trace of `stores16 base k` from `rsp = p`. -/
def storesTr (p : Addr) (base : Nat) : Nat → List Leak
  | 0 => []
  | k + 1 => .addr (p + BitVec.ofNat 64 (base + 16 * k)) :: storesTr p base k

/-- The trace of `chunkStores b` from `rsp = p`. -/
def chunkTr (p : Addr) (b : Nat) : List Leak :=
  storesTr p (b % 16) (b / 16) ++ (if b % 16 = 8 then [.addr p] else [])

theorem ea_rsp (u : State) (off : Nat) :
    u.ea { base := .rsp, disp := (off : Int) } = u.gpr .rsp + BitVec.ofNat 64 off := by
  simp [State.ea, BitVec.ofInt_natCast]

theorem ea_rsp2 (u : State) (a k : Nat) :
    u.ea { base := .rsp, disp := (a : Int) + 16 * (k : Int) } = u.gpr .rsp + BitVec.ofNat 64 (a + 16 * k) := by
  rw [show (a : Int) + 16 * (k : Int) = ((a + 16 * k : Nat) : Int) by push_cast; rfl, ea_rsp]

theorem off_lt (x p : Addr) (o n : Nat) (ho : o + n < 2 ^ 64) :
    (x - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ (x - p).toNat ∧ (x - p).toNat < o + n := by
  have e : (x - (p + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o = x - p := by bv_omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)] at e'
  have h1 := (x - (p + BitVec.ofNat 64 o)).isLt
  have h2 := (x - p).isLt
  generalize (x - (p + BitVec.ofNat 64 o)).toNat = r at *
  generalize (x - p).toNat = d at *
  by_cases hc : r + o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc] at e'; omega
  · rw [show r + o = (r + o - 2 ^ 64) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at e'
    omega

theorem writeW_zero128 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 128) x = if (x - a).toNat < 16 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

theorem stores16_run (b base : Nat) (hb : b < 2 ^ 64) : ∀ (k : Nat) (u : State),
    ⟨u.gpr .rsp, b⟩ ∈ u.wr → u.xmm .xmm0 = 0 → base + 16 * k ≤ b →
    ∃ m', execBlock isa (stores16 base k) u = some ({ u with mem := m' }, storesTr (u.gpr .rsp) base k) ∧
      (∀ x, ((x - u.gpr .rsp).toNat < base ∨ base + 16 * k ≤ (x - u.gpr .rsp).toNat) → m' x = u.mem x) ∧
      (∀ x, base ≤ (x - u.gpr .rsp).toNat → (x - u.gpr .rsp).toNat < base + 16 * k → m' x = 0)
  | 0, u, _, _, _ => ⟨u.mem, rfl, fun _ _ => rfl, fun _ h₁ h₂ => absurd h₂ (by omega)⟩
  | k + 1, u, hR, hx, hk => by
    have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k)) 16 := by
      refine ⟨_, hR, ?_⟩
      simp only [Region.Contains]
      rw [show u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k) - u.gpr .rsp = BitVec.ofNat 64 (base + 16 * k) by
        bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    let a := u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k)
    let u₁ : State := { u with mem := u.mem.writeW a (u.xmm .xmm0) }
    obtain ⟨m', he, hout, hin'⟩ := stores16_run b base hb k u₁ hR hx (by omega)
    refine ⟨m', ?_, fun x hx' => ?_, fun x h₁ h₂ => ?_⟩
    · simp only [stores16, execBlock, isa, reduceExec, zero16, ea_rsp, State.store128, hin, ↓reduceIte]
      rw [show ({ u with mem := u.mem.writeW a (u.xmm .xmm0) } : State) = u₁ from rfl, he]
      simp [storesTr, addrs, ea_rsp2, u₁]
    · have hw : u₁.mem x = u.mem x := by
        simp only [u₁, hx, writeW_zero128]
        rw [ite_eq_right]; rw [off_lt _ _ _ _ (by omega)]; omega
      rw [hout x (by simp only [u₁]; omega), hw]
    · by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * k
      · exact hin' x h₁ hc
      · rw [hout x (by simp only [u₁]; omega)]
        simp only [u₁, hx, writeW_zero128]
        rw [ite_eq_left]; rw [off_lt _ _ _ _ (by omega)]; omega

theorem chunk_run (b : Nat) (hb : b < 2 ^ 64) (h8 : b % 8 = 0) (u : State)
    (hR : ⟨u.gpr .rsp, b⟩ ∈ u.wr) (hx : u.xmm .xmm0 = 0) (hr : u.gpr .r11 = 0) :
    ∃ m', execBlock isa (chunkStores b) u = some ({ u with mem := m' }, chunkTr (u.gpr .rsp) b) ∧
      (∀ x, b ≤ (x - u.gpr .rsp).toNat → m' x = u.mem x) ∧
      (∀ x, (x - u.gpr .rsp).toNat < b → m' x = 0) := by
  obtain ⟨m₁, he, hout, hin⟩ := stores16_run b (b % 16) hb (b / 16) u hR hx (by omega)
  have hbb : b % 16 + 16 * (b / 16) = b := by omega
  rw [hbb] at hout hin
  unfold chunkStores store8s
  rw [execBlock_append, he]
  by_cases h16 : b % 16 = 8
  · have h0 : BitVec.ofInt 64 0 = 0 := rfl
    have hin8 : InRegions u.wr (u.gpr .rsp) 8 := by
      refine ⟨_, hR, ?_⟩; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have hea : u.gpr .rsp + BitVec.ofInt 64 0 = u.gpr .rsp := by rw [h0]; bv_omega
    refine ⟨m₁.writeW (u.gpr .rsp) (u.gpr .r11), ?_, fun x hx' => ?_, fun x hx' => ?_⟩
    · simp only [h16, ↓reduceIte, Option.bind_some, execBlock, isa, reduceExec, State.store64, State.ea,
        hea, hin8]
      simp [chunkTr, h16, addrs, State.ea]
    · simp only [Mem.writeW, Mem.write]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      exact hout x (Or.inr hx')
    · simp only [Mem.writeW, Mem.write, hr]
      split
      · simp
      · rename_i hn
        exact hin x (by omega) hx'
  · refine ⟨m₁, ?_, fun x hx' => hout x (Or.inr hx'), fun x hx' => ?_⟩
    · simp [h16, execBlock, chunkTr]
    · exact hin x (by omega) hx'

theorem below_split (p : Addr) (b n : Nat) (h : b + n ≤ p.toNat) (x : Addr) :
    (⟨p - BitVec.ofNat 64 (b + n), b + n⟩ : Region).Contains x 1 ↔
      (x - (p - BitVec.ofNat 64 b)).toNat < b ∨
        (⟨p - BitVec.ofNat 64 b - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize p.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := b + n) (by omega), Nat.mod_eq_of_lt (a := b) (by omega),
    Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

/-- The trace of `wipe cs` from `rsp = p`. -/
def wipeTr : List Nat → Addr → List Leak
  | [], _ => []
  | b :: bs, p => chunkTr (p - BitVec.ofNat 64 b) b ++ wipeTr bs (p - BitVec.ofNat 64 b)

theorem wipe_run : ∀ (cs : List Nat) (u : State), (∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) →
    cs.sum ≤ (u.gpr .rsp).toNat → u.xmm .xmm0 = 0 → u.gpr .r11 = 0 →
    ∃ m', Exec isa (wipe cs) u (wipeTr cs (u.gpr .rsp)) { u with mem := m' } ∧
      (∀ x, ¬ (⟨u.gpr .rsp - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
      (∀ x, (⟨u.gpr .rsp - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 → m' x = 0)
  | [], u, _, _, _, _ =>
    ⟨u.mem, .block rfl, fun _ _ => rfl, fun x hx => by simp [Region.Contains] at hx⟩
  | b :: bs, u, hv, hs, hx, hr => by
    obtain ⟨hb0, hb4, hb8⟩ := hv b (List.mem_cons_self ..)
    simp only [List.sum_cons] at hs
    let p := u.gpr .rsp
    let q := p - BitVec.ofNat 64 b
    let u₁ : State := { u.setReg .rsp q with wr := ⟨q, b⟩ :: u.wr }
    have hpush : isa.push (.alloc b) u = some u₁ := by
      simp only [isa, push, u₁, q, p]; rw [ite_eq_left ⟨hb0, hb4, hb8, by omega⟩]
    have hq : u₁.gpr .rsp = q := by simp [u₁, State.setReg]
    obtain ⟨m₁, he₁, ho₁, hi₁⟩ := chunk_run b (by omega) hb8 u₁ (by rw [hq]; simp [u₁])
      (by simpa [u₁, State.setReg] using hx) (by simpa [u₁, State.setReg] using hr)
    let u₂ : State := { u₁ with mem := m₁ }
    have hqn : bs.sum ≤ q.toNat := by
      have := p.isLt
      have h' : b + bs.sum ≤ p.toNat := hs
      simp only [q, BitVec.toNat_sub, BitVec.toNat_ofNat]
      generalize p.toNat = P at *
      rw [Nat.mod_eq_of_lt (a := b) (by omega)]
      omega
    obtain ⟨m₂, he₂, ho₂, hi₂⟩ := wipe_run bs u₂ (fun b' h => hv b' (List.mem_cons_of_mem _ h))
      (by simpa [u₂, hq] using hqn) (by simpa [u₂, u₁, State.setReg] using hx)
      (by simpa [u₂, u₁, State.setReg] using hr)
    have hpop : isa.pop (.free b) u₁ { u₂ with mem := m₂ } = some { u with mem := m₂ } := by
      simp only [isa, pop, u₂]
      split
      rotate_left
      · rename_i hn; exact (hn ⟨hb0, hb4, hb8, trivial, trivial, by simp [u₁, State.setReg]⟩).elim
      congr 1
      simp only [u₁, State.setReg, State.mk.injEq, and_true, List.tail_cons]
      funext r
      by_cases h : r = .rsp
      · subst h; simp [q, p, BitVec.sub_add_cancel]
      · simp [h]
    refine ⟨m₂, ?_, fun x hx' => ?_, fun x hx' => ?_⟩
    · have e := Exec.frame (M := isa) hpush (.seq (.block he₁) he₂) hpop
      have htr : wipeTr (b :: bs) p = (isa.addrs (.alloc b) u).map Leak.addr ++
          (chunkTr (u₁.gpr .rsp) b ++ wipeTr bs (u₂.gpr .rsp)) ++
          (isa.addrs (.free b) { u₂ with mem := m₂ }).map Leak.addr := by
        simp [wipeTr, addrs, u₂, hq, q]
      rw [htr]; exact e
    · have hs' : b + bs.sum ≤ p.toNat := hs
      rw [List.sum_cons, below_split p b bs.sum hs'] at hx'
      simp only [not_or] at hx'
      rw [ho₂ x (by simpa [u₂, hq] using hx'.2)]
      exact ho₁ x (by rw [hq]; exact Nat.le_of_not_lt hx'.1)
    · have hs' : b + bs.sum ≤ p.toNat := hs
      rw [List.sum_cons, below_split p b bs.sum hs'] at hx'
      by_cases h2 : (⟨q - BitVec.ofNat 64 bs.sum, bs.sum⟩ : Region).Contains x 1
      · exact hi₂ x (by simpa [u₂, hq] using h2)
      · rw [ho₂ x (by simpa [u₂, hq] using h2)]
        exact hi₁ x (by rw [hq]; rcases hx' with h | h; exacts [h, absurd h h2])

/-! ## Clearing the registers -/

/-- The state after zeroing the SSE registers `xs` at level `v`. -/
def clearedV (v : VecLevel) (xs : List XReg) (s : State) : State :=
  { s with
    xmm := fun x => if x ∈ xs then 0 else s.xmm x
    ymmHi := fun x => if v = .avx ∧ x ∈ xs then 0 else s.ymmHi x
    zmmHi := fun x => if v = .avx ∧ x ∈ xs then 0 else s.zmmHi x }

theorem execBlock_vecs (v : VecLevel) (xs : List XReg) (s : State) :
    execBlock isa (xs.map (zeroX v)) s = some (clearedV v xs s, []) := by
  induction xs generalizing s with
  | nil => simp [execBlock, clearedV]
  | cons x xs ih =>
    cases v
    all_goals
      simp only [List.map_cons, execBlock, zeroX, isa, reduceExec, ih, Option.map_some, addrs,
        List.map_nil, List.nil_append]
      simp only [clearedV, XOp.exec, VOp.exec, State.setXmm, State.setV, XBinOp.eval, VBinOp.sse,
        BitVec.xor_self, List.mem_cons, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.mk.injEq, true_and, and_true]
      first
        | (funext y; by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;> simp [h1, h2])
        | (refine ⟨?_, ?_, ?_⟩ <;> funext y <;> by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;>
            simp [h1, h2])

/-- The state after zeroing the general-purpose registers `rs` with `xor`. -/
def clearedG (rs : List Reg) (s : State) : State :=
  { s with
    gpr := fun r => if r ∈ rs then 0 else s.gpr r
    cf := some false, of := some false, zf := some true, sf := some false }

theorem execBlock_gprs (rs : List Reg) (hrs : rs ≠ []) (s : State) :
    execBlock isa (rs.map zeroR) s = some (clearedG rs s, []) := by
  induction rs generalizing s with
  | nil => exact absurd rfl hrs
  | cons r rs ih =>
    simp only [List.map_cons, execBlock, zeroR, isa, reduceExec, addrs, srcAddrs, execAlu32, readSrc32,
      Option.bind_some, BitVec.xor_self, List.map_nil, List.nil_append]
    by_cases hn : rs = []
    · subst hn
      simp only [List.map_nil, execBlock, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_singleton]
      simp
    · rw [ih hn]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_cons]
      simp only [State.mk.injEq, and_true]
      funext y; by_cases h1 : y = r <;> by_cases h2 : y ∈ rs <;> simp [h1, h2]

/-- What `retFix retBits` leaves in `rax`. -/
def retVal (retBits : Nat) (x : BitVec 64) : BitVec 64 :=
  if retBits = 0 then 0
  else if retBits < 32 then ((x.setWidth 32) &&& BitVec.ofNat 32 (2 ^ retBits - 1)).setWidth 64
  else if retBits = 32 then (x.setWidth 32).setWidth 64
  else x

theorem execBlock_clearGpr (rb : Nat) (s : State) :
    execBlock isa (clearGpr rb) s =
      some (clearedG scratchRegs (s.setReg .rax (retVal rb (s.gpr .rax))), []) := by
  have hne : scratchRegs ≠ [] := by decide
  unfold clearGpr retFix retVal
  by_cases h0 : rb = 0
  · simp only [h0, ↓reduceIte, List.singleton_append]
    rw [show zeroR .rax :: scratchRegs.map zeroR = (Reg.rax :: scratchRegs).map zeroR from rfl,
      execBlock_gprs _ (by decide)]
    simp only [clearedG, State.setReg, Option.some.injEq, Prod.mk.injEq, and_true, State.mk.injEq]
    funext r; by_cases hr : r = .rax
    · subst hr; simp [scratchRegs]
    · simp [hr]
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, execAlu32, readSrc32,
      Option.bind_some, addrs, srcAddrs, execBlock_gprs _ hne, Option.map_some, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg,
      ]
    try (funext r; by_cases hr : r = .rax <;> simp [hr, scratchRegs])
  by_cases h2 : rb = 32
  · subst h2
    simp only [h0, h1, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, readSrc32,
      Option.map_some, addrs, srcAddrs, execBlock_gprs _ hne, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [clearedG, State.setReg32, State.setReg]
    try (funext r; by_cases hr : r = .rax <;> simp [hr, scratchRegs])
  · simp only [h0, h1, h2, ↓reduceIte, List.nil_append, execBlock_gprs _ hne, Option.some.injEq,
      Prod.mk.injEq, and_true]
    simp only [clearedG, State.setReg, State.mk.injEq, and_true]
    funext r; by_cases hr : r = .rax
    · subst hr; simp [scratchRegs]
    · simp [hr]

/-- The state `scrubTail v rb cs` leaves, given the memory `m'` its wipe leaves. -/
def finState (v : VecLevel) (rb : Nat) (m' : Mem) (u : State) : State :=
  clearedG scratchRegs
    (({ clearedG [.r11] (clearedV v xregs u) with mem := m' } : State).setReg .rax (retVal rb (u.gpr .rax)))

theorem mem_xregs (x : XReg) : x ∈ xregs := by cases x <;> decide

theorem tail_run (v : VecLevel) (rb : Nat) (cs : List Nat) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat) :
    ∃ m', Exec isa (scrubTail v rb cs) u (wipeTr cs (u.gpr .rsp)) (finState v rb m' u) ∧
      (∀ x, ¬ (⟨u.gpr .rsp - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
      (∀ x, (⟨u.gpr .rsp - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 → m' x = 0) := by
  let u₁ := clearedG [.r11] (clearedV v xregs u)
  have h₁ : execBlock isa (clearVec v ++ [zeroR .r11]) u = some (u₁, []) := by
    rw [execBlock_append, clearVec, execBlock_vecs]
    simp only [Option.bind_some]
    rw [show [zeroR .r11] = [Reg.r11].map zeroR from rfl, execBlock_gprs _ (by decide)]
    rfl
  have hsp : u₁.gpr .rsp = u.gpr .rsp := rfl
  obtain ⟨m', he, ho, hi⟩ := wipe_run cs u₁ hv hs (by simp [u₁, clearedG, clearedV, mem_xregs])
    (by simp [u₁, clearedG])
  refine ⟨m', ?_, ho, hi⟩
  have h₃ := execBlock_clearGpr rb { u₁ with mem := m' }
  have e := Exec.seq (M := isa) (.block h₁) (.seq he (.block h₃))
  simp only [List.nil_append, List.append_nil, hsp] at e
  exact e

/-! ## What `Sig.contract` gives -/

/-- What `Verified.scrub` needs of the calling convention a contract is for:
`abi`'s, possibly with tables of constants (`Abi.withConsts`), which add
readable regions apart from the stack the function uses, and with tables of
functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 64
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → (n = 0 ∨ n ≤ (s.gpr .rsp).toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .rax
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  have h6 : argRegs.length = 6 := rfl
  simp only [abi] at h
  split at h <;> cases h
  · rename_i hl; simp only [List.length_map, List.length_take]; omega
  · rename_i hl; simp only [List.length_append, List.length_map, List.length_range]; omega

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    n = 0 ∨ n ≤ (s.gpr .rsp).toNat := by
  simp only [abi] at h
  split at h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h.1

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ _ h => ⟨abi_wf_stack h, fun _ hr hn => absurd hr hn⟩,
    fun _ _ h => h, fun _ => rfl, fun _ => rfl, fun _ _ h => h, abi_args_len⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1, fun _ => rfl, fun _ => rfl,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨abi_wf_stack hw, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.mem, hA.ret, hA.rdSub, hA.argsLen⟩

/-- The calling convention of every x86-64 artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi ((abi.withConsts cs).withTables sig ts) :=
  (ScrubAbi.consts cs).tables sig ts

/-! ## What `Sig.contract` gives -/

theorem contract_pre_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    (stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) ∧
      ∀ r ∈ s.rd ++ s.wr, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧
        (stack ≠ 0 → (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint r) := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨hst, hcon⟩ := hA.wf _ _ _ hwf
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have key : ∀ r ∈ s.rd ++ s.wr, ∀ q ∈ abi.reserved stack s, q.Disjoint r := by
    intro r hr q hq
    rcases List.mem_append.mp hr with hr | hr
    · by_cases hn : r ∈ A.rd s
      · rw [hrd] at hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        exact hres' q hq a (List.mem_filter.mp ha).1
      · exact hcon r hr hn q hq
    · rw [← hA.wr, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hres' q hq a (List.mem_filter.mp ha).1
  refine ⟨hst, fun r hr => ⟨key r hr _ (by simp [abi]), fun hn => key r hr _ ?_⟩⟩
  cases stack with
  | zero => exact absurd rfl hn
  | succ n => simp [abi, stackBelow]

theorem contract_pub_rsp {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.gpr .rsp = s₂.gpr .rsp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

/-! ## The result -/

theorem retVal_low {rb : Nat} (hrb : rb ≤ 32 ∨ rb = 64) (x : BitVec 64) :
    (retVal rb x).setWidth rb = x.setWidth rb := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, retVal]
  by_cases h0 : rb = 0
  · subst h0; simp [Nat.mod_one]
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2 ^ rb - 1) (by have := Nat.pow_lt_pow_right (a := 2) (by omega) h1; omega),
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
      Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 32 % 2 ^ rb) (by
        have := Nat.mod_lt (x.toNat % 2 ^ 32) (Nat.two_pow_pos rb)
        have := Nat.pow_le_pow_right (n := 2) (by omega) (show rb ≤ 64 by omega); omega),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  by_cases h2 : rb = 32
  · subst h2; simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]
  · have : rb = 64 := by omega
    subst this; simp

theorem retVal_hi {rb : Nat} (hrb : rb ≤ 32 ∨ rb = 64) (x : BitVec 64) : retVal rb x >>> rb = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, retVal, Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  by_cases h0 : rb = 0
  · subst h0; simp
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2 ^ rb - 1) (by have := Nat.pow_lt_pow_right (a := 2) (by omega) h1; omega),
      Nat.and_two_pow_sub_one_eq_mod]
    have h3 := Nat.mod_lt (x.toNat % 2 ^ 32) (Nat.two_pow_pos rb)
    have := Nat.pow_le_pow_right (n := 2) (by omega) (show rb ≤ 64 by omega)
    rw [Nat.mod_eq_of_lt (by omega)]; exact h3
  by_cases h2 : rb = 32
  · subst h2; simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth]
    have := Nat.mod_lt x.toNat (Nat.two_pow_pos 32)
    rw [Nat.mod_eq_of_lt (by omega)]; exact this
  · have : rb = 64 := by omega
    subst this; simp only [h0, h1, h2, ↓reduceIte]; exact x.isLt

/-- How `scrub` clears the vector registers, as an instruction level. -/
def _root_.VG.Impl.Scrub.X86_64.VecLevel.level : VecLevel → Nat
  | .sse => 0
  | .avx => 1

/-! ## The theorem -/

theorem finState_gpr {v : VecLevel} {rb : Nat} {m' : Mem} {u : State} {r : Reg}
    (h₁ : r ∉ scratchRegs) (h₂ : r ≠ .rax) : (finState v rb m' u).gpr r = u.gpr r := by
  have h₃ : r ≠ .r11 := fun h => h₁ (by subst h; decide)
  simp [finState, clearedG, clearedV, State.setReg, h₁, h₂, h₃]

theorem slot_not_below {sp x : Addr} {n : Nat} (hn : n + 8 < 2 ^ 64)
    (hx : (⟨sp, 8⟩ : Region).Contains x 1) : ¬ (⟨sp - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have := sp.isLt; have := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
  generalize sp.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- Code verified against a contract that `Sig.contract` derives, whose
frames and calls use at most `stack` bytes, run by `scrub`, which clears
`cs.sum = stack` bytes of stack: verified against the same contract, and
without secret residue, if the postcondition reads the memory on return only
within the buffers (`hpost`). -/
theorem Verified.scrub {c : Prog isa} {v : VecLevel} {cs : List Nat} (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hlv : ∀ i ∈ instrs c, i.vecLevel ≤ v.level)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u') :
    Verified target (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) cs c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) cs c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  -- What a run of `c`, then of the clearing, gives.
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧
      u.gpr .rsp = s.gpr .rsp ∧ cs.sum ≤ (u.gpr .rsp).toNat := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    refine ⟨ha, hp, hr, ?_⟩
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  -- The clearing's run.
  have tail : ∀ s t u s' t', (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      Exec isa (Impl.Scrub.X86_64.scrubTail v (sig.retBits A.ptrBits) cs) u t' s' →
      ∃ m', t' = wipeTr cs (s.gpr .rsp) ∧ s' = finState v (sig.retBits A.ptrBits) m' u ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = 0) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, ho, hi⟩ := tail_run v (sig.retBits A.ptrBits) cs u hv hl
    obtain ⟨rfl, rfl⟩ := Exec.det het e
    rw [hr, hcs] at ho hi
    exact ⟨m', by rw [hr], rfl, ho, hi⟩
  -- Buffers are not in the stack the clearing wipes.
  have outB : ∀ s, (sig.contract A pre post wa stack leak).pre s → ∀ x,
      (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) →
        ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 := by
    intro s hs x ⟨r, hr, hx⟩ hb
    by_cases h0 : stack = 0
    · subst h0; simp [Region.Contains] at hb
    · exact ((contract_pre_scrub hA hs).2 r hr).2 h0 x hb hx
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hr, hl⟩ := run s t u hs he
    obtain ⟨m', et, hmo, hmi⟩ := tail_run v (sig.retBits A.ptrBits) cs u hv hl
    rw [hr, hcs] at hmo hmi
    refine ⟨_, _, .seq he et, ⟨fun r hr' => ?_, ?_, ?_⟩, ?_⟩
    · rw [finState_gpr (by revert hr'; revert r; decide) (by revert hr'; revert r; decide)]
      exact ha.1 r hr'
    · rw [← ha.2.1]
      apply Mem.readW_congr
      intro i hi
      simp only [finState, clearedG, State.setReg]
      exact hmo _ (slot_not_below hst (by
        simp only [Region.Contains]
        rw [show s.gpr .rsp + BitVec.ofNat 64 i - s.gpr .rsp = BitVec.ofNat 64 i by
          rw [BitVec.add_comm, BitVec.add_sub_cancel], BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [Nat.reduceDiv] at hi; omega))
    · exact ha.2.2
    · refine hpost s u _ hs hq (fun x hx => hmo x (outB s hs x hx)) ?_
      simp only [finState, clearedG, State.setReg]
      simp only [show Reg.rax ∉ scratchRegs by decide, ↓reduceIte]
      exact retVal_low hrb _
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, rfl, -⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, rfl, -⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_rsp hA hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, -, rfl, hmo₁, hmi₁⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, -, rfl, hmo₂, hmi₂⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    obtain ⟨ha₁, -, -, -⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, -, -⟩ := run s₂ _ _ h₂ a₂
    obtain ⟨hrd, hwr, hg, -, -, -, -, -, -, hy, hz, hyH, hzH, hmx, hm⟩ := ho
    have hsp' : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
    have rw₁ := Exec.rdwr a₁
    have rw₂ := Exec.rdwr a₂
    have k1₁ := Exec.vecKeep1 (fun i hi => by have := hlv i hi; cases v <;> simp [VecLevel.level] at this ⊢ <;> omega) a₁
    have k1₂ := Exec.vecKeep1 (fun i hi => by have := hlv i hi; cases v <;> simp [VecLevel.level] at this ⊢ <;> omega) a₂
    simp only [vk1, Prod.mk.injEq] at k1₁ k1₂
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    refine ⟨?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
    · show u₁.rd = u₂.rd; rw [rw₁.1, rw₂.1, hrd]
    · show u₁.wr = u₂.wr; rw [rw₁.2, rw₂.2, hwr]
    · by_cases hs : r ∈ scratchRegs
      · have h11 : r ≠ .rax := hr
        simp [finState, clearedG, hs]
      · rw [finState_gpr hs hr, finState_gpr hs hr, ha₁.1 r (cs_ r hs hr), ha₂.1 r (cs_ r hs hr)]
        exact hg r hr
    · simp only [finState, clearedG, State.setReg, show Reg.rax ∉ scratchRegs by decide, ↓reduceIte]
      rw [retVal_hi hrb, retVal_hi hrb]
    · funext x; simp [finState, clearedG, State.setReg, clearedV, mem_xregs]
    · cases v
      · have k₁ := Exec.vecKeep0 (fun i hi => by simpa [VecLevel.level] using hlv i hi) a₁
        have k₂ := Exec.vecKeep0 (fun i hi => by simpa [VecLevel.level] using hlv i hi) a₂
        simp only [vk0, Prod.mk.injEq] at k₁ k₂
        funext x
        simp only [finState, clearedG, State.setReg, clearedV, reduceCtorEq, false_and, ↓reduceIte,
          k₁.2.2.2.1, k₂.2.2.2.1, hy]
      · funext x; simp [finState, clearedG, State.setReg, clearedV, mem_xregs]
    · cases v
      · have k₁ := Exec.vecKeep0 (fun i hi => by simpa [VecLevel.level] using hlv i hi) a₁
        have k₂ := Exec.vecKeep0 (fun i hi => by simpa [VecLevel.level] using hlv i hi) a₂
        simp only [vk0, Prod.mk.injEq] at k₁ k₂
        funext x
        simp only [finState, clearedG, State.setReg, clearedV, reduceCtorEq, false_and, ↓reduceIte,
          k₁.2.2.2.2, k₂.2.2.2.2, hz]
      · funext x; simp [finState, clearedG, State.setReg, clearedV, mem_xregs]
    · show u₁.ymmH = u₂.ymmH; rw [k1₁.1, k1₂.1, hyH]
    · show u₁.zmmHiH = u₂.zmmHiH; rw [k1₁.2.1, k1₂.2.1, hzH]
    · show u₁.mxcsr = u₂.mxcsr; rw [k1₁.2.2, k1₂.2.2, hmx]
    · show m₁ x = m₂ x
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
        have : (finState v (sig.retBits A.ptrBits) m₁ u₁).rd ++ (finState v (sig.retBits A.ptrBits) m₁ u₁).wr =
          s₁.rd ++ s₁.wr := by show u₁.rd ++ u₁.wr = _; rw [rw₁.1, rw₁.2]
        rw [← this]; exact hx
      by_cases hb : (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1
      · rw [hmi₁ x hb, hmi₂ x (hsp' ▸ hb)]
      · have nd : ∀ sp : Addr, sp = s₁.gpr .rsp →
            ¬ (⟨sp - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩ : Region).Contains x 1 := by
          rintro sp rfl hc; exact hb (below_sub hd (by omega) x hc)
        have nw : ∀ r ∈ s₁.wr, ¬ r.Contains x 1 := fun r hr => hx' r (List.mem_append_right _ hr)
        rw [hmo₁ x hb, hmo₂ x (hsp' ▸ hb),
          f₁ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r hr
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ rfl),
          f₂ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r (hwr ▸ hr)
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ hsp'.symm)]
        exact hm x hx'

end

/-! ## Registering scrubbed code -/

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits (`Verified.scrub`'s `hpost`). -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .rax).setWidth rb = (u.gpr .rax).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

theorem stores16_spSafe (base : Nat) : ∀ k, (stores16 base k).all (fun i => !isa.writesSp i) = true
  | 0 => rfl
  | k + 1 => by simp only [stores16, List.all_cons, stores16_spSafe base k, Bool.and_true]; rfl

theorem wipe_spSafe : ∀ cs : List Nat, (wipe cs).all (fun i => !isa.writesSp i) = true
  | [] => rfl
  | b :: bs => by
    simp only [wipe, Code.all, chunkStores, List.all_append, stores16_spSafe, wipe_spSafe bs,
      Bool.true_and, Bool.and_true, store8s]
    split <;> rfl

theorem scrub_spSafe {c : Prog isa} (v : VecLevel) (rb : Nat) (cs : List Nat)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrub v rb cs c).all (fun i => !isa.writesSp i) = true := by
  have hv : (clearVec v ++ [zeroR .r11]).all (fun i => !isa.writesSp i) = true := by
    cases v <;> rfl
  have hg : (clearGpr rb).all (fun i => !isa.writesSp i) = true := by
    unfold clearGpr retFix
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  rw [scrub, scrubTail]
  simp only [Code.all]
  rw [h, hv, wipe_spSafe cs, hg]
  rfl

theorem chunksAux_spec : ∀ f n, n / 4080 < f →
    (chunksAux f n).sum = n ∧ ∀ b ∈ chunksAux f n, 0 < b ∧ b ≤ 4080 ∧ (n % 8 = 0 → b % 8 = 0)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => ⟨rfl, fun _ h => by simp [chunksAux] at h⟩
  | f + 1, n + 1, h => by
    simp only [chunksAux]
    split
    · exact ⟨by simp, fun b hb => by simp at hb; subst hb; omega⟩
    · obtain ⟨hs, hv⟩ := chunksAux_spec f (n + 1 - 4080) (by omega)
      refine ⟨by rw [List.sum_cons, hs]; omega, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have := hv b hb; omega

theorem chunks_sum (n : Nat) : (chunks n).sum = n := (chunksAux_spec _ n (by omega)).1

theorem chunks_valid {n : Nat} (h8 : n % 8 = 0) : ∀ b ∈ chunks n, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
  fun b hb => by have := (chunksAux_spec _ n (by omega)).2 b hb; omega

/-- `r`, scrubbed: its code followed by the clearing (`scrub`), at level `v`,
with `r.stack` bytes of stack wiped. -/
def scrubReg {api : Api} (r : Registration api target) (v : VecLevel)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) (chunks r.stack) r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    rw [e] at hv hp ⊢
    exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
      (chunks_sum r.stack) hst (chunks_valid h8)
      (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb hp).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ r.spSafe
  features := r.features
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro

theorem scrubReg_noResidue {api : Api} (r : Registration api target) (v : VecLevel)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) (hw : r.written = []) :
    NoResidue (scrubReg r v hd hst h8 hlv hrb hpost hw).code r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  show NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) (chunks r.stack) r.code) r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
  rw [e] at hv hp ⊢
  exact (Verified.scrub (ScrubAbi.of r.consts api.sig r.tables) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs hlv i hi) hrb hp).2

end VG.X86_64.Scrub
