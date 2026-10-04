import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.ChaCha20.X86.Vqr
import VerifiedGarbage.Proof.ChaCha20.X86.Bytes

/-!
# ChaCha20 on x86 (32-bit): four blocks at once with SSE2

Doubleword `l` of each slot of `buf` (and of each register) holds a word of
block `l`; each quarter round of the code is the specification's on each of
the four blocks. During the rounds a word is in its slot or in a register
(`Loc`); one lemma (`step_ok`) covers every quarter round of `plan`, whose
loads, registers and stores are checked against where the words are by
evaluation (`stepOk`). The output XORs each 16 bytes of keystream into the
data if they lie within it, and stores the 16 bytes that run past its end in
`buf[0, 16)` (`chunk_ok`).
-/

namespace VG.Proof.ChaCha20.X86.Quad

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86.Bytes (byte_write16 cmpi_ok)

/-! ## The slots -/

/-- `buf`, as far as the four-block code uses it. -/
abbrev bufR (buf : Addr) : Region := ⟨buf, 320⟩

/-- The slots of the sixteen words, `buf[0, 256)`. -/
abbrev slotsR (buf : Addr) : Region := ⟨buf, 256⟩

/-- The four states `vs 0, …, vs 3` are in the slots: word `k` of state `l`
in doubleword `l` of slot `k`. -/
def Holds4 (buf : Addr) (vs : Nat → CState) (m : Mem) : Prop :=
  ∀ k (hk : k < 16) l, l < 4 → m.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (vs l)[k]

theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

theorem ea_withMem (s : State) (m : Mem) (o : MemOp) : ({ s with mem := m } : State).ea o = s.ea o := rfl

theorem ea_gpr {s s' : State} (h : s'.gpr = s.gpr) (m : MemOp) : s'.ea m = s.ea m := by
  simp only [State.ea, h]

theorem in_buf {rs ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions (rs ++ ws) (buf + BitVec.ofNat 64 d) n :=
  ⟨bufR buf, List.mem_append_right _ hw, Offset.contains_base buf h (by lit_omega)⟩

theorem out_buf {ws : List Region} {buf : Addr} (hw : bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions ws (buf + BitVec.ofNat 64 d) n :=
  ⟨bufR buf, hw, Offset.contains_base buf h (by lit_omega)⟩

theorem lane_load (m : Mem) (buf : Addr) (d : Nat) {l : Nat} (hl : l < 4) :
    dword (m.readW (buf + BitVec.ofNat 64 d) 128) l = m.readW (buf + BitVec.ofNat 64 (d + 4 * l)) 32 := by
  rw [dword_readW _ _ hl, Offset.add_add]

theorem lane_write_self (m : Mem) (buf : Addr) (v : BitVec 128) (d : Nat) {l : Nat} (hl : l < 4) :
    (m.writeW (buf + BitVec.ofNat 64 d) v).readW (buf + BitVec.ofNat 64 (d + 4 * l)) 32 = dword v l := by
  rw [← Offset.add_add, readW_writeW128 _ _ _ hl]

theorem lane_write_other (m : Mem) (buf : Addr) (v : BitVec 128) {d e : Nat} (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 16 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 16 ≤ d) :
    (m.writeW (buf + BitVec.ofNat 64 e) v).readW (buf + BitVec.ofNat 64 d) 32 =
      m.readW (buf + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep buf h (by lit_omega) (by lit_omega)) (by decide)

theorem slots_frame_write {rs : List Region} {m m' : Mem} {buf : Addr} (h : Frame rs m m')
    (hr : slotsR buf ∈ rs) (v : BitVec 128) {k : Nat} (hk : k < 16) :
    Frame rs m (m'.writeW (buf + BitVec.ofNat 64 (slot k)) v) :=
  h.writeW hr _ (Offset.contains_base buf (by simp only [slot]; omega) (by simp only [slot]; lit_omega))

/-! ## One quarter round on the four states -/

theorem lane_qr {m : Mem} {buf : Addr} {vs : Nat → CState} (h : Holds4 buf vs m) {x : Nat}
    (hx : x < 16) {l : Nat} (hl : l < 4) :
    dword (m.readW (buf + BitVec.ofNat 64 (slot x)) 128) l = (vs l)[x] := by
  rw [lane_load _ _ _ hl]; exact h x hx l hl

/-- Reading lane `l` of slot `k` after writing slot `k'`. -/
theorem lane_other (m : Mem) (buf : Addr) (v : BitVec 128) {k k' l : Nat} (hk : k < 16)
    (hk' : k' < 16) (hl : l < 4) (h : k' ≠ k) :
    (m.writeW (buf + BitVec.ofNat 64 (slot k')) v).readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 =
      m.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 :=
  lane_write_other _ _ _ (by lit_omega) (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem lane_self (m : Mem) (buf : Addr) (v : BitVec 128) (k : Nat) {l : Nat} (hl : l < 4) :
    (m.writeW (buf + BitVec.ofNat 64 (slot k)) v).readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 =
      dword v l :=
  lane_write_self _ _ _ _ hl

/-! ## Words in registers

During the rounds, word `k` of the four states is in its slot or, doubleword
`l` for block `l`, in a register (`L k`). -/

/-- Where each word is: in a register, or in its slot (`none`). -/
abbrev Loc := Nat → Option XReg

/-- `L` with word `k` at `v`. -/
def upd (L : Loc) (k : Nat) (v : Option XReg) : Loc := fun j => if j = k then v else L j

/-- Word `k` of block `l`, where `L` says it is. -/
def val (buf : Addr) (L : Loc) (s : State) (k l : Nat) : Word :=
  match L k with
  | some r => dword (s.xmm r) l
  | none => s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32

/-- The four states `vs` are where `L` says. -/
def HoldsR (buf : Addr) (L : Loc) (vs : Nat → CState) (s : State) : Prop :=
  ∀ k (hk : k < 16) l, l < 4 → val buf L s k l = (vs l)[k]

theorem val_some {buf : Addr} {L : Loc} {s : State} {k : Nat} {r : XReg} (h : L k = some r) (l : Nat) :
    val buf L s k l = dword (s.xmm r) l := by
  simp only [val, h]

theorem val_none {buf : Addr} {L : Loc} {s : State} {k : Nat} (h : L k = none) (l : Nat) :
    val buf L s k l = s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 := by
  simp only [val, h]

theorem HoldsR.congr {buf : Addr} {L L' : Loc} {vs : Nat → CState} {s : State}
    (he : ∀ j, j < 16 → L j = L' j) (h : HoldsR buf L vs s) : HoldsR buf L' vs s := fun k hk l hl => by
  rw [← h k hk l hl]; simp only [val, he k hk]

/-- The loads of a quarter round: each word into a register not in use. -/
def loadsOk : Loc → List (XReg × Nat) → Bool
  | _, [] => true
  | L, p :: ps => decide (p.2 < 16 ∧ L p.2 = none ∧ ∀ j : Nat, j < 16 → L j ≠ some p.1) &&
      loadsOk (upd L p.2 (some p.1)) ps

def loadsLoc : Loc → List (XReg × Nat) → Loc
  | L, [] => L
  | L, p :: ps => loadsLoc (upd L p.2 (some p.1)) ps

/-- The stores of a quarter round: each word from the register it is in. -/
def storesOk : Loc → List (Nat × XReg) → Bool
  | _, [] => true
  | L, p :: ps => decide (p.1 < 16 ∧ L p.1 = some p.2) && storesOk (upd L p.1 none) ps

def storesLoc : Loc → List (Nat × XReg) → Loc
  | L, [] => L
  | L, p :: ps => storesLoc (upd L p.1 none) ps

/-- The quarter round on `x, y, z, w`: they are in `q`'s registers, distinct
and not `xmm7`, which hold no other word; no word is in `xmm7`. -/
def quadOk (L : Loc) (q : QStep) (x y z w : Nat) : Bool := decide (
  L x = some q.a ∧ L y = some q.b ∧ L z = some q.c ∧ L w = some q.d ∧
  q.a ≠ q.b ∧ q.a ≠ q.c ∧ q.a ≠ q.d ∧ q.b ≠ q.c ∧ q.b ≠ q.d ∧ q.c ≠ q.d ∧
  q.a ≠ .xmm7 ∧ q.b ≠ .xmm7 ∧ q.c ≠ .xmm7 ∧ q.d ≠ .xmm7 ∧
  (∀ j : Nat, j < 16 → L j ≠ some .xmm7) ∧
  ∀ j : Nat, j < 16 → j = x ∨ j = y ∨ j = z ∨ j = w ∨
    (L j ≠ some q.a ∧ L j ≠ some q.b ∧ L j ≠ some q.c ∧ L j ≠ some q.d))

def stepOk (L : Loc) (q : QStep) (x y z w : Nat) : Bool :=
  loadsOk L q.loads && quadOk (loadsLoc L q.loads) q x y z w && storesOk (loadsLoc L q.loads) q.stores

def stepLoc (L : Loc) (q : QStep) : Loc := storesLoc (loadsLoc L q.loads) q.stores

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (buf : Addr) (L : Loc) (vs : Nat → CState) (s₀ s : State) : Prop where
  holds : HoldsR buf L vs s
  frame : Frame [slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem RI.congr {buf : Addr} {L L' : Loc} {vs : Nat → CState} {s₀ s : State}
    (he : ∀ j, j < 16 → L j = L' j) (h : RI buf L vs s₀ s) : RI buf L' vs s₀ s :=
  ⟨h.holds.congr he, h.frame, h.gpr, h.rd, h.wr⟩

/-- `buf[288, 320)`, where a quarter round may keep constants. -/
abbrev kR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 288, 32⟩

/-- What the four-block code needs of its quarter round `k.qr`: that it
computes the quarter round given what `k.init` leaves in `buf[288, 320)`
(`Inv`), which only writes there undo. -/
structure KernelOk (k : Kernel) where
  Inv : Addr → Mem → Prop
  inv_frame : ∀ {buf : Addr} {m m' : Mem} {rs : List Region}, Inv buf m → Frame rs m m' →
    (∀ r ∈ rs, (kR buf).Disjoint r) → Inv buf m'
  qr_ok : ∀ {buf : Addr} {a b c d : XReg}, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    a ≠ .xmm7 → b ≠ .xmm7 → c ≠ .xmm7 → d ≠ .xmm7 → ∀ s : State,
    (∀ e, e < 320 → s.ea (at_ .edi e) = buf + BitVec.ofNat 64 e) → bufR buf ∈ s.wr → Inv buf s.mem →
    WP isa (.block (k.qr a b c d)) s (QrPost a b c d s)
  init_ok : ∀ {buf : Addr} (s : State), (∀ e, e < 320 → s.ea (at_ .edi e) = buf + BitVec.ofNat 64 e) →
    bufR buf ∈ s.wr → WP isa (.block k.init) s fun s' => Inv buf s'.mem ∧ Frame [kR buf] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem kR_slots (buf : Addr) : (kR buf).Disjoint (slotsR buf) := Offset.disjoint_base _ (by decide) (by decide)

section
variable {buf : Addr} {s₀ : State} (hb : ∀ d, d < 320 → s₀.ea (at_ .edi d) = buf + BitVec.ofNat 64 d)
  (hwb : bufR buf ∈ s₀.wr)
include hb hwb

theorem ld_ok {L : Loc} {vs : Nat → CState} {s : State} {r : XReg} {k : Nat} (hk : k < 16)
    (hn : L k = none) (hr : ∀ j, j < 16 → L j ≠ some r) (h : RI buf L vs s₀ s) :
    WP isa (.block [ld r k]) s (RI buf (upd L k (some r)) vs s₀) := by
  have e := (ea_gpr h.gpr _).trans (hb (slot k) (by simp only [slot]; omega))
  have i := in_buf (rs := s.rd) (h.wr ▸ hwb) (d := slot k) (n := 16) (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, e, i, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj l hl => ?_, h.frame, h.gpr, h.rd, h.wr⟩
  have hv := h.holds j hj l hl
  by_cases hjk : j = k
  · subst hjk
    rw [val_some (show upd L j (some r) j = some r from ite_eq_left rfl), RegUpd.xmm_setXmm_self,
      lane_load _ _ _ hl, ← hv, val_none hn]
    rfl
  · have hu : upd L k (some r) j = L j := ite_eq_right hjk
    rcases hL : L j with _ | r'
    · rw [val_none (hu.trans hL)]; rw [val_none hL] at hv; exact hv
    · rw [val_some (hu.trans hL), RegUpd.xmm_setXmm_of_ne _ _ fun e => hr j hj (by rw [hL, e])]
      rw [val_some hL] at hv; exact hv

theorem loads_ok {vs : Nat → CState} : ∀ (ps : List (XReg × Nat)) (L : Loc) (s : State),
    loadsOk L ps = true → RI buf L vs s₀ s →
    WP isa (.block (ps.map fun p => ld p.1 p.2)) s (RI buf (loadsLoc L ps) vs s₀)
  | [], _, _, _, h => WP.block_nil h
  | p :: ps, L, s, hok, h => by
    simp only [loadsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk, hn, hr⟩, hok⟩ := hok
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    exact WP.mono (ld_ok hb hwb hk hn hr h) fun s₁ h₁ => loads_ok ps _ s₁ hok h₁

theorem st_ok {L : Loc} {vs : Nat → CState} {s : State} {r : XReg} {k : Nat} (hk : k < 16)
    (hs : L k = some r) (h : RI buf L vs s₀ s) :
    WP isa (.block [st k r]) s (RI buf (upd L k none) vs s₀) := by
  have e := (ea_gpr h.gpr _).trans (hb (slot k) (by simp only [slot]; omega))
  have o : InRegions s.wr (buf + BitVec.ofNat 64 (slot k)) 16 := by
    rw [h.wr]; exact out_buf hwb (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, e, o, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj l hl => ?_, slots_frame_write h.frame (List.mem_singleton_self _) _ hk, h.gpr,
    h.rd, h.wr⟩
  have hv := h.holds j hj l hl
  by_cases hjk : j = k
  · subst hjk
    rw [val_none (show upd L j none j = none from ite_eq_left rfl)]
    show (s.mem.writeW _ _).readW _ _ = _
    rw [lane_self _ _ _ _ hl, ← hv, val_some hs]
  · have hu : upd L k none j = L j := ite_eq_right hjk
    rcases hL : L j with _ | r'
    · rw [val_none (hu.trans hL)]
      show (s.mem.writeW _ _).readW _ _ = _
      rw [lane_other _ _ _ hj hk hl (Ne.symm hjk), ← hv, val_none hL]
    · rw [val_some (hu.trans hL)]; rw [val_some hL] at hv; exact hv

theorem stores_ok {vs : Nat → CState} : ∀ (ps : List (Nat × XReg)) (L : Loc) (s : State),
    storesOk L ps = true → RI buf L vs s₀ s →
    WP isa (.block (ps.map fun p => st p.1 p.2)) s (RI buf (storesLoc L ps) vs s₀)
  | [], _, _, _, h => WP.block_nil h
  | p :: ps, L, s, hok, h => by
    simp only [storesOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk, hs⟩, hok⟩ := hok
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    exact WP.mono (st_ok hb hwb hk hs h) fun s₁ h₁ => stores_ok ps _ s₁ hok h₁

theorem quad_ok {k : Kernel} (K : KernelOk k) (hinv : K.Inv buf s₀.mem) {L : Loc} {q : QStep}
    {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hok : quadOk L q x y z w = true) {vs : Nat → CState} {s : State}
    (h : RI buf L vs s₀ s) :
    WP isa (.block (k.qr q.a q.b q.c q.d)) s
      (RI buf L (fun l => qround (vs l) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  simp only [quadOk, decide_eq_true_eq] at hok
  obtain ⟨hLa, hLb, hLc, hLd, hab, hac, had, hbc, hbd, hcd, ha7, hb7, hc7, hd7, h7, ho⟩ := hok
  refine WP.mono (K.qr_ok hab hac had hbc hbd hcd ha7 hb7 hc7 hd7 s
      (fun e he => (ea_gpr h.gpr _).trans (hb e he)) (h.wr ▸ hwb)
      (K.inv_frame hinv h.frame (by simpa using kR_slots buf)))
    fun s' ⟨hv, hx', hg, hm, hr, hwr⟩ => ⟨fun k hk l hl => ?_, hm ▸ h.frame, hg.trans h.gpr,
      hr.trans h.rd, hwr.trans h.wr⟩
  obtain ⟨ea, eb, ec, ed⟩ := hv l hl
  have vx : dw s q.a l = (vs l)[x] := by rw [← h.holds x hx l hl, val_some hLa]
  have vy : dw s q.b l = (vs l)[y] := by rw [← h.holds y hy l hl, val_some hLb]
  have vz : dw s q.c l = (vs l)[z] := by rw [← h.holds z hz l hl, val_some hLc]
  have vw : dw s q.d l = (vs l)[w] := by rw [← h.holds w hw l hl, val_some hLd]
  rw [vx, vy, vz, vw] at ea eb ec ed
  rw [qround_get _ _ _ _ _ k hk]
  simp only
  by_cases e4 : w = k
  · subst e4; rw [ite_eq_left rfl, val_some hLd]; exact ed
  by_cases e3 : z = k
  · subst e3; rw [ite_eq_right e4, ite_eq_left rfl, val_some hLc]; exact ec
  by_cases e2 : y = k
  · subst e2; rw [ite_eq_right e4, ite_eq_right e3, ite_eq_left rfl, val_some hLb]; exact eb
  by_cases e1 : x = k
  · subst e1; rw [ite_eq_right e4, ite_eq_right e3, ite_eq_right e2, ite_eq_left rfl, val_some hLa]
    exact ea
  rw [ite_eq_right e4, ite_eq_right e3, ite_eq_right e2, ite_eq_right e1, ← h.holds k hk l hl]
  rcases hL : L k with _ | r
  · rw [val_none hL, val_none hL, hm]
  · obtain ⟨na, nb, nc, nd⟩ : L k ≠ some q.a ∧ L k ≠ some q.b ∧ L k ≠ some q.c ∧ L k ≠ some q.d := by
      rcases ho k hk with e | e | e | e | e
      · exact absurd e.symm e1
      · exact absurd e.symm e2
      · exact absurd e.symm e3
      · exact absurd e.symm e4
      · exact e
    rw [val_some hL, val_some hL, hx' r (fun e => na (by rw [hL, e])) (fun e => nb (by rw [hL, e]))
      (fun e => nc (by rw [hL, e])) (fun e => nd (by rw [hL, e])) (fun e => h7 k hk (by rw [hL, e]))]

theorem step_ok {k : Kernel} (K : KernelOk k) (hinv : K.Inv buf s₀.mem) {L : Loc} {q : QStep}
    {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hok : stepOk L q x y z w = true) {vs : Nat → CState} {s : State}
    (h : RI buf L vs s₀ s) :
    WP isa (.block (q.code k)) s
      (RI buf (stepLoc L q) (fun l => qround (vs l) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  simp only [stepOk, Bool.and_eq_true] at hok
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hok
  rw [QStep.code, WP.block_append_iff, WP.block_append_iff]
  exact WP.mono (loads_ok hb hwb _ _ s h₁ h) fun s₁ r₁ =>
    WP.mono (quad_ok hb hwb K hinv hx hy hz hw h₂ r₁) fun s₂ r₂ => stores_ok hb hwb _ _ s₂ h₃ r₂

end

/-! ## Double rounds -/

/-- The quarter rounds of `plan`. -/
abbrev qs (i : Nat) : QStep := plan.getD i ⟨[], .xmm0, .xmm0, .xmm0, .xmm0, []⟩

/-- The loads of `cached`. -/
def enter : List (XReg × Nat) := cached.map fun p => (p.2, p.1)

/-- Where the words are between double rounds. -/
def loc₀ : Loc := loadsLoc (fun _ => none) enter

/-- Where the words are before quarter round `i` of a double round. -/
def locs : Nat → Loc
  | 0 => loc₀
  | i + 1 => stepLoc (locs i) (qs i)

theorem locs_8 : ∀ j, j < 16 → locs 8 j = loc₀ j := by decide

/-- The rounds invariant with every word in its slot. -/
abbrev RI4 (buf : Addr) (vs : Nat → CState) (s₀ s : State) : Prop := RI buf (fun _ => none) vs s₀ s

section
variable {buf : Addr} {s₀ : State} (hb : ∀ d, d < 320 → s₀.ea (at_ .edi d) = buf + BitVec.ofNat 64 d)
  (hwb : bufR buf ∈ s₀.wr)
include hb hwb

theorem doubleRound4_ok {k : Kernel} (K : KernelOk k) (hinv : K.Inv buf s₀.mem) {vs : Nat → CState}
    {s : State} (h : RI buf loc₀ vs s₀ s) :
    WP isa (doubleRound4 k) s (RI buf loc₀ (fun l => innerBlock (vs l)) s₀) := by
  unfold doubleRound4
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 0) (q := qs 0) (x := 0) (y := 4) (z := 8) (w := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide) h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 1) (q := qs 1) (x := 1) (y := 5) (z := 9) (w := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) h1) fun _ h2 => ?_)
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 2) (q := qs 2) (x := 2) (y := 6) (z := 10) (w := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 3) (q := qs 3) (x := 3) (y := 7) (z := 11) (w := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) h3) fun _ h4 => ?_)
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 4) (q := qs 4) (x := 0) (y := 5) (z := 10) (w := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 5) (q := qs 5) (x := 1) (y := 6) (z := 11) (w := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide) h5) fun _ h6 => ?_)
  refine WP.seq (WP.mono (step_ok hb hwb K hinv (L := locs 6) (q := qs 6) (x := 2) (y := 7) (z := 8) (w := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) h6) fun _ h7 => ?_)
  exact WP.mono (step_ok hb hwb K hinv (L := locs 7) (q := qs 7) (x := 3) (y := 4) (z := 9) (w := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) h7) fun _ h8 => h8.congr locs_8

theorem rounds4_ok {k : Kernel} (K : KernelOk k) (hinv : K.Inv buf s₀.mem) {vs : Nat → CState}
    {s : State} (h : RI buf loc₀ vs s₀ s) :
    ∀ n, WP isa (rounds4 k n) s (RI buf loc₀ (fun l => Nat.repeat innerBlock n (vs l)) s₀)
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (rounds4_ok K hinv h n) fun _ h' => doubleRound4_ok hb hwb K hinv h')

omit hb hwb in
theorem enter_eq : cached.map (fun p => ld p.2 p.1) = enter.map fun p => ld p.1 p.2 := rfl

theorem rounds_ok {k : Kernel} (K : KernelOk k) (hinv : K.Inv buf s₀.mem) {vs : Nat → CState}
    (h : Holds4 buf vs s₀.mem) :
    WP isa (rounds10 k) s₀ (RI4 buf (fun l => Nat.repeat innerBlock 10 (vs l)) s₀) := by
  unfold rounds10
  rw [enter_eq]
  refine WP.seq (WP.mono (loads_ok hb hwb (vs := vs) enter (fun _ => none) s₀ (by decide)
    ⟨h, Frame.refl _ _, rfl, rfl, rfl⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (rounds4_ok hb hwb K hinv h₁ 10) fun s₂ h₂ => ?_)
  exact WP.mono (stores_ok hb hwb cached loc₀ s₂ (by decide) h₂) fun _ h₃ => h₃.congr (by decide)

end

/-! ## The context -/

open VG.Spec.ChaCha20 (stateAt serialize)

/-- The state, 64 bytes at `st`. -/
abbrev stR (st : Addr) : Region := ⟨st, 64⟩

/-- Where `ebx` and `edi` point (`state` and `buf`), and what the code may
access there. -/
structure Ctx (st buf : Addr) (s : State) : Prop where
  eaS : ∀ d, d < 64 → s.ea (at_ .ebx d) = st + BitVec.ofNat 64 d
  eaB : ∀ d, d < 320 → s.ea (at_ .edi d) = buf + BitVec.ofNat 64 d
  wst : stR st ∈ s.wr
  wb : bufR buf ∈ s.wr
  sb : (stR st).Disjoint (bufR buf)

theorem Ctx.of {st buf : Addr} {s s' : State} (h : Ctx st buf s) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : Ctx st buf s' :=
  ⟨fun d hd => (ea_gpr hg _).trans (h.eaS d hd), fun d hd => (ea_gpr hg _).trans (h.eaB d hd),
    hw ▸ h.wst, hw ▸ h.wb, h.sb⟩

theorem in_st {rs ws : List Region} {st : Addr} (hw : stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (st + BitVec.ofNat 64 d) n :=
  ⟨stR st, List.mem_append_right _ hw, Offset.contains_base st h (by lit_omega)⟩

theorem out_st {ws : List Region} {st : Addr} (hw : stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (st + BitVec.ofNat 64 d) n :=
  ⟨stR st, hw, Offset.contains_base st h (by lit_omega)⟩

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (stR p).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by lit_omega) (by lit_omega)) hd (by decide)

/-- Doubleword `i` of row `r` of a state in memory. -/
theorem row_lane (m : Mem) (st : Addr) {r i : Nat} (hr : r < 4) (hi : i < 4) :
    dword (m.readW (st + BitVec.ofNat 64 (16 * r)) 128) i = (stateAt m st)[4 * r + i]'(by omega) := by
  rw [lane_load _ _ _ hi]
  simp only [stateAt, Vector.getElem_ofFn]
  exact congrArg (fun d => m.readW (st + BitVec.ofNat 64 d) 32) (by omega)

theorem ctr_get (S : CState) (j : Nat) {k : Nat} (hk : k < 16) :
    (ctr S j)[k] = if k = 12 then S[12] + BitVec.ofNat 32 j else S[k] := by
  simp only [ctr, Vector.getElem_set]
  by_cases h : k = 12
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## The setup -/

/-- The words below `n` of the four states `vs` are in their slots, and only
the slots have been written since `s₀`. -/
structure Done (buf : Addr) (vs : Nat → CState) (n : Nat) (s₀ s : State) : Prop where
  done : ∀ k (hk : k < 16), k < n → ∀ l, l < 4 →
    s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (vs l)[k]
  frame : Frame [slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Row `r` of the state `C`, in `xmm4`. -/
def Row4 (C : CState) (r : Nat) (s : State) : Prop :=
  ∀ i (hi : i < 4) (hr : r < 4), dword (s.xmm .xmm4) i = C[4 * r + i]'(by omega)

section
variable {st buf : Addr} {s₀ : State} (hc : Ctx st buf s₀)
include hc

theorem setupWord_ok {r i : Nat} (hr : r < 4) (hi : i < 4) {s : State}
    (h : Done buf (fun _ => stateAt s₀.mem st) (4 * r + i) s₀ s)
    (hx : Row4 (stateAt s₀.mem st) r s) :
    WP isa (.block [bcast .xmm0 .xmm4 i, .movdquStore (at_ .edi (slot (4 * r + i))) .xmm0]) s
      fun s' => Done buf (fun _ => stateAt s₀.mem st) (4 * r + (i + 1)) s₀ s' ∧
        Row4 (stateAt s₀.mem st) r s' := by
  have e := (ea_gpr h.gpr _).trans (hc.eaB (slot (4 * r + i)) (by simp only [slot]; omega))
  have o : InRegions s.wr (buf + BitVec.ofNat 64 (slot (4 * r + i))) 16 := by
    rw [h.wr]; exact out_buf hc.wb (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [bcast, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.store128,
    ea_setXmm, e, RegUpd.wr_setXmm, o, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun k hk hkn l hl => ?_, ?_, ?_, ?_, ?_⟩, fun j hj hr' => ?_⟩
  · simp only [RegUpd.mem_setXmm]
    by_cases hke : k = 4 * r + i
    · subst hke
      rw [lane_self _ _ _ _ hl, RegUpd.xmm_setXmm_self, dword_shufDwords_bcast _ hi hl,
        hx i hi hr]
    · rw [lane_other _ _ _ hk (by omega) hl (Ne.symm hke)]
      exact h.done k hk (by omega) l hl
  · exact slots_frame_write h.frame (List.mem_singleton_self _) _ (by omega)
  · exact h.gpr
  · exact h.rd
  · exact h.wr
  · simp only [RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]; exact hx j hj hr'

theorem setupRow_ok {r : Nat} (hr : r < 4) {s : State}
    (h : Done buf (fun _ => stateAt s₀.mem st) (4 * r) s₀ s) :
    WP isa (.block (setupRow r)) s (Done buf (fun _ => stateAt s₀.mem st) (4 * r + 4) s₀) := by
  have e := (ea_gpr h.gpr _).trans (hc.eaS (16 * r) (by omega))
  have i : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [h.wr]; exact in_st hc.wst (by omega)
  have hS : stateAt s.mem st = stateAt s₀.mem st := stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]
    exact hc.sb.sub_right (Region.sub_prefix (by lit_omega)))
  rw [setupRow, ← List.singleton_append, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, e, i, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  have h₀ : Done buf (fun _ => stateAt s₀.mem st) (4 * r + 0) s₀
      (s.setXmm .xmm4 (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128)) ∧
      Row4 (stateAt s₀.mem st) r (s.setXmm .xmm4 (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128)) :=
    ⟨⟨fun k hk hkn l hl => h.done k hk hkn l hl, h.frame, h.gpr, h.rd, h.wr⟩, fun j hj hr' => by
      rw [RegUpd.xmm_setXmm_self, row_lane _ _ hr' hj, hS]⟩
  exact WP.mono (wp_range_flatMap (M := isa)
    (fun i s => Done buf (fun _ => stateAt s₀.mem st) (4 * r + i) s₀ s ∧ Row4 (stateAt s₀.mem st) r s)
    (fun i s hi hs => setupWord_ok hc hr hi hs.1 hs.2) 4 (Nat.le_refl _) _ h₀) fun _ h' => h'.1

/-- The counters `c + l` (from word 12 of `C`) at `ctrOff`. -/
def Ctrs (buf : Addr) (C : CState) (n : Nat) (m : Mem) : Prop :=
  ∀ l, l < n → m.readW (buf + BitVec.ofNat 64 (ctrOff + 4 * l)) 32 = C[12] + BitVec.ofNat 32 l

/-- `buf[272, 288)`, the counters. -/
abbrev ctrR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 ctrOff, 16⟩

/-- Before lane `n` of the counters. -/
structure CI (buf : Addr) (C : CState) (n : Nat) (s₀ s : State) : Prop where
  slots : ∀ k (hk : k < 16) l, l < 4 → (k ≠ 12 ∨ l < n) →
    s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (ctr C l)[k]
  ctrs : Ctrs buf C n s.mem
  eax : s.gpr .eax = C[12] + BitVec.ofNat 32 n
  frame : Frame [slotsR buf, ctrR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hc in
theorem w32_other (m : Mem) (buf : Addr) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (buf + BitVec.ofNat 64 e) v).readW (buf + BitVec.ofNat 64 d) 32 =
      m.readW (buf + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep buf h (by lit_omega) (by lit_omega)) (by decide)

theorem ctrLane_ok {C : CState} {l : Nat} (hl : l < 4) {s : State} (h : CI buf C l s₀ s) :
    WP isa (.block (ctrLane l)) s (CI buf C (l + 1) s₀) := by
  have hdi : s.gpr .edi = s₀.gpr .edi := h.keep _ (by decide)
  have e₁ : addr (s₀.gpr .edi) (slot 12 + 4 * l) = buf + BitVec.ofNat 64 (16 * 12 + 4 * l) :=
    hc.eaB _ (by simp only [slot]; omega)
  have e₂ : addr (s₀.gpr .edi) (ctrOff + 4 * l) = buf + BitVec.ofNat 64 (ctrOff + 4 * l) :=
    hc.eaB _ (by simp only [ctrOff]; omega)
  have o₁ : InRegions s.wr (addr (s₀.gpr .edi) (slot 12 + 4 * l)) 4 := by
    rw [e₁, h.wr]; exact out_buf hc.wb (by omega)
  refine Wp.wp_stm hdi o₁ fun s₁ u₁ => ?_
  have o₂ : InRegions s₁.wr (addr (s₀.gpr .edi) (ctrOff + 4 * l)) 4 := by
    rw [e₂, u₁.wr, h.wr]; exact out_buf hc.wb (by simp only [ctrOff]; omega)
  refine Wp.wp_stm (by rw [u₁.gpr, hdi]) o₂ fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => WP.block_nil ?_
  have hm : s₃.mem = (s.mem.writeW (buf + BitVec.ofNat 64 (16 * 12 + 4 * l)) (s.gpr .eax)).writeW
      (buf + BitVec.ofNat 64 (ctrOff + 4 * l)) (s.gpr .eax) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₁.gpr, e₁, e₂]
  refine ⟨fun k hk l' hl' hkl => ?_, fun l' hl' => ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [hm, w32_other (d := 16 * k + 4 * l') (e := ctrOff + 4 * l) _ _ _ (by lit_omega) (by simp only [ctrOff]; lit_omega)
      (by simp only [ctrOff]; omega)]
    by_cases he : k = 12 ∧ l' = l
    · obtain ⟨rfl, rfl⟩ := he
      rw [Mem.readW_writeW_self32, h.eax, ctr_get _ _ hk, ite_eq_left rfl]
    · rw [w32_other (d := 16 * k + 4 * l') (e := 16 * 12 + 4 * l) _ _ _ (by lit_omega) (by lit_omega) (by omega)]
      exact h.slots k hk l' hl' (by omega)
  · rw [hm]
    by_cases he : l' = l
    · subst he; rw [Mem.readW_writeW_self32, h.eax]
    · rw [w32_other (d := ctrOff + 4 * l') (e := ctrOff + 4 * l) _ _ _ (by simp only [ctrOff]; lit_omega) (by simp only [ctrOff]; lit_omega)
        (by simp only [ctrOff]; omega),
        w32_other (d := ctrOff + 4 * l') (e := 16 * 12 + 4 * l) _ _ _ (by simp only [ctrOff]; lit_omega) (by lit_omega)
        (by simp only [ctrOff]; omega)]
      exact h.ctrs l' (by omega)
  · rw [u₃.gpr, u₂.gpr, u₁.gpr, h.eax, Offset.add_ofNat_add_one]
  · rw [hm]
    refine (h.frame.writeW (List.mem_cons_self ..) _ (Offset.contains_base buf (by omega) (by lit_omega))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_
    exact Offset.contains buf (by omega) (by omega) (by simp only [ctrOff]; lit_omega)
  · rw [u₃.other r hr, u₂.gpr, u₁.gpr, h.keep r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]

/-- What the setup leaves: the four states in the slots, the counters at
`ctrOff`, and everything else as it was (but `eax`). -/
structure SPost (buf : Addr) (C : CState) (s₀ s : State) : Prop where
  holds : Holds4 buf (fun l => ctr C l) s.mem
  ctrs : Ctrs buf C 4 s.mem
  frame : Frame [slotsR buf, ctrR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup4_ok : WP isa (.block setup4) s₀ (SPost buf (stateAt s₀.mem st) s₀) := by
  rw [setup4, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun r s => Done buf (fun _ => stateAt s₀.mem st) (4 * r) s₀ s)
    (fun r s hr hs => setupRow_ok hc hr hs) 4 (Nat.le_refl _) s₀
    ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, rfl, rfl⟩) fun s h => ?_
  have hb : s.gpr .ebx = s₀.gpr .ebx := by rw [h.gpr]
  have e : addr (s₀.gpr .ebx) 48 = st + BitVec.ofNat 64 48 := hc.eaS 48 (by decide)
  have hS : stateAt s.mem st = stateAt s₀.mem st := stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]
    exact hc.sb.sub_right (Region.sub_prefix (by lit_omega)))
  have v : s.mem.readW (st + BitVec.ofNat 64 48) 32 = (stateAt s₀.mem st)[12] := by
    rw [← hS]; simp [stateAt]
  rw [setupCtr, ← List.singleton_append]
  refine Wp.wp_ldm hb (by rw [e, h.rd, h.wr]; exact in_st hc.wst (by decide)) fun s₁ u₁ => ?_
  rw [e, v] at u₁
  have c₀ : CI buf (stateAt s₀.mem st) 0 s₀ s₁ :=
    ⟨fun k hk l hl hkl => by
      have hk12 : k ≠ 12 := by omega
      rw [u₁.mem, h.done k hk (by omega) l hl, ctr_get _ _ hk, ite_eq_right hk12],
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [u₁.gpr]; simp,
      by rw [u₁.mem]; exact h.frame.mono (by simp), fun r hr => by rw [u₁.other r hr, h.gpr],
      by rw [u₁.rd, h.rd], by rw [u₁.wr, h.wr]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun l s => CI buf (stateAt s₀.mem st) l s₀ s)
    (fun l s hl hs => ctrLane_ok hc hl hs) 4 (Nat.le_refl _) s₁ c₀) fun s' h' => ?_
  exact ⟨fun k hk l hl => h'.slots k hk l hl (by omega), h'.ctrs, h'.frame, h'.keep, h'.rd, h'.wr⟩

end

/-! ## The output: loading a row -/

theorem xr_ne : ∀ i, i < 4 → ∀ j, j < 4 → i ≠ j → xr i ≠ xr j := by decide
theorem xr_ne45 : ∀ i, i < 4 → xr i ≠ .xmm4 ∧ xr i ≠ .xmm5 := by decide

/-- Words `4 r, …, 4 r + 3` of the four states `vs` are in their slots. -/
def RowHolds (buf : Addr) (vs : Nat → CState) (r : Nat) (m : Mem) : Prop :=
  ∀ i (hi : i < 4) (hr : r < 4) l, l < 4 →
    m.readW (buf + BitVec.ofNat 64 (16 * (4 * r + i) + 4 * l)) 32 = (vs l)[4 * r + i]'(by omega)

theorem loadRow_ok {st buf : Addr} {r : Nat} (hr : r < 4) {vs : Nat → CState} {s : State}
    (hc : Ctx st buf s) (hh : RowHolds buf vs r s.mem) :
    WP isa (.block (loadRow r)) s fun s' =>
      (∀ i (hi : i < 4) l, l < 4 → dword (s'.xmm (xr i)) l = (vs l)[4 * r + i]) ∧
      Row4 (stateAt s.mem st) r s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 := hc.eaB (slot (4 * r)) (by simp only [slot]; omega)
  have e1 := hc.eaB (slot (4 * r + 1)) (by simp only [slot]; omega)
  have e2 := hc.eaB (slot (4 * r + 2)) (by simp only [slot]; omega)
  have e3 := hc.eaB (slot (4 * r + 3)) (by simp only [slot]; omega)
  have e4 := hc.eaS (16 * r) (by omega)
  have i0 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r)) (n := 16) (by simp only [slot]; omega)
  have i1 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 1)) (n := 16) (by simp only [slot]; omega)
  have i2 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 2)) (n := 16) (by simp only [slot]; omega)
  have i3 := in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 3)) (n := 16) (by simp only [slot]; omega)
  have i4 := in_st (rs := s.rd) hc.wst (d := 16 * r) (n := 16) (by omega)
  apply WP.of_runBlock
  simp only [loadRow, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_setXmm,
    e0, e1, e2, e3, e4, i0, i1, i2, i3, i4, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi l hl => ?_, fun j hj hr' => ?_, trivial, trivial, trivial, trivial⟩
  · rcases cases4 hi with rfl | rfl | rfl | rfl <;>
      simp only [xr, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true] <;>
      rw [lane_load _ _ _ hl]
    · exact hh 0 (by decide) hr l hl
    · exact hh 1 (by decide) hr l hl
    · exact hh 2 (by decide) hr l hl
    · exact hh 3 (by decide) hr l hl
  · simp only [RegUpd.xmm_setXmm_self]; exact row_lane _ _ hr' hj

/-! ## Adding the input states -/

/-- While adding the input states to row `r`: `xr j` holds words `4 r + j`
of the four states `vs`, plus those of the input states `ctr C l` if
`j < i`; `xmm4` holds row `r` of `C`; nothing else has changed since `s₁`
(but XMM registers). -/
structure AW (vs : Nat → CState) (C : CState) (r i : Nat) (s₁ s : State) : Prop where
  regs : ∀ j (hj : j < 4) (hr : r < 4) l, l < 4 → dword (s.xmm (xr j)) l =
    if j < i then (vs l)[4 * r + j] + (ctr C l)[4 * r + j] else (vs l)[4 * r + j]
  row : Row4 C r s
  mem : s.mem = s₁.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem addWord_ok {st buf : Addr} {vs : Nat → CState} {C : CState} {r i : Nat} (hr : r < 4)
    (hi : i < 4) {s₁ s : State} (hc : Ctx st buf s₁) (hct : Ctrs buf C 4 s₁.mem)
    (h : AW vs C r i s₁ s) : WP isa (.block (addWord4 r i)) s (AW vs C r (i + 1) s₁) := by
  -- The value added to `xr i`: word `4 r + i` of the input states.
  suffices hadd : WP isa (.block (addWord4 r i)) s fun s' =>
      (∀ l, l < 4 → dword (s'.xmm (xr i)) l = dword (s.xmm (xr i)) l + (ctr C l)[4 * r + i]) ∧
      (∀ x, x ≠ xr i → x ≠ .xmm5 → s'.xmm x = s.xmm x) ∧
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr by
    refine WP.mono hadd fun s' ⟨ha, ho, hm, hg, hrd, hwr⟩ => ⟨fun j hj _ l hl => ?_, fun j hj hr' => ?_,
      hm.trans h.mem, hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr⟩
    · by_cases hji : j = i
      · subst hji
        rw [ha l hl, h.regs j hj hr l hl, ite_eq_right (Nat.lt_irrefl j), ite_eq_left (Nat.lt_succ_self j)]
      · rw [ho _ (xr_ne j hj i hi hji) (xr_ne45 j hj).2, h.regs j hj hr l hl]
        by_cases hj' : j < i
        · rw [ite_eq_left hj', ite_eq_left (by omega)]
        · rw [ite_eq_right hj', ite_eq_right (by omega)]
    · rw [ho _ (xr_ne45 i hi).1.symm (by decide)]; exact h.row j hj hr'
  have hgx := xr_ne45 i hi
  by_cases h3 : r = 3 ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := h3
    have e := (ea_gpr h.gpr _).trans (hc.eaB ctrOff (by decide))
    have i5 : InRegions (s.rd ++ s.wr) (buf + BitVec.ofNat 64 ctrOff) 16 := by
      rw [h.rd, h.wr]; exact in_buf hc.wb (by decide)
    rw [show addWord4 3 0 = [.movdquLoad .xmm5 (at_ .edi ctrOff), xb .paddd .xmm0 .xmm5] from rfl]
    apply WP.of_runBlock
    simp only [xb, xr, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, State.load128, e, i5, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
      RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl => ?_, fun x h0 h5 => ?_, trivial, trivial, trivial, trivial⟩
    · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
        dword_paddd _ _ hl]
      rw [lane_load _ _ _ hl, h.mem, hct l hl, ctr_get _ _ (by decide), ite_eq_left rfl]
    · simp only [RegUpd.xmm_setXmm_of_ne, h0, h5, not_false_eq_true]
  · apply WP.of_runBlock
    simp only [addWord4, h3, ite_false, xb, bcast, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl => ?_, fun x h0 h5 => ?_, trivial, trivial, trivial, trivial⟩
    · rw [RegUpd.xmm_setXmm_self, dword_paddd _ _ hl, RegUpd.xmm_setXmm_of_ne _ _ hgx.2,
        RegUpd.xmm_setXmm_self, dword_shufDwords_bcast _ hi hl, h.row i hi hr,
        ctr_get _ _ (by omega), ite_eq_right (by omega)]
    · rw [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h5]

/-! ## Transposing -/

theorem transpose_ok (s : State) :
    WP isa (.block transpose) s fun s' =>
      (∀ l, l < 4 → ∀ j, j < 4 → dword (s'.xmm (outReg l)) j = dword (s.xmm (xr j)) l) ∧
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [transpose, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl j hj => ?_, trivial, trivial, trivial, trivial⟩
  rcases cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [outReg, xr, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq,
      not_false_eq_true, eval_movdqa, punpcklqdq_eq, punpckhqdq_eq, punpckldq_eq, punpckhdq_eq,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3] <;>
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-! ## XORing 16 bytes into the data -/

/-- The data of one iteration: `W ≤ 256` bytes. -/
abbrev dW (a : Addr) (W : Nat) : Region := ⟨a, W⟩

/-- `buf[0, 16)`, where the keystream for the last bytes of the data is
stored: by then, the code has read the slot. -/
abbrev stashR (buf : Addr) : Region := ⟨buf, 16⟩

/-- Where `esi` points (the data of the iteration, `W` bytes), and that the
code may write it. -/
structure DCtx (a : Addr) (W : Nat) (s : State) : Prop where
  eaD : ∀ d, d < W → s.ea (at_ .esi d) = a + BitVec.ofNat 64 d
  wd : ∀ off n, off + n ≤ W → InRegions s.wr (a + BitVec.ofNat 64 off) n

theorem DCtx.of {a : Addr} {W : Nat} {s s' : State} (h : DCtx a W s) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : DCtx a W s' :=
  ⟨fun d hd => (ea_gpr hg _).trans (h.eaD d hd), fun off n h' => hw ▸ h.wd off n h'⟩

theorem xor16_ok {x : XReg} (hx : x ≠ .xmm6) {W off : Nat} (hW : W ≤ 256) (ho : off + 16 ≤ W) {a : Addr}
    {s : State} (hd : DCtx a W s) :
    WP isa (.block (xor16 x off)) s fun s' =>
      (∀ k, k < W → s'.mem (a + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ (s.xmm x).extractLsb' (8 * (k - off)) 8
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [dW a W] s.mem s'.mem ∧ (∀ r, r ≠ .xmm6 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := hd.eaD off (by omega)
  have o : InRegions s.wr (a + BitVec.ofNat 64 off) 16 := hd.wd off 16 ho
  have i : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 :=
    let ⟨r, hr, hc⟩ := o; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [xor16, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, ea_setXmm, e, i, RegUpd.wr_setXmm, o, ite_true, RegUpd.mem_setXmm,
    RegUpd.gpr_setXmm, RegUpd.rd_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base a ho (by lit_omega)), fun r hr => ?_, trivial, trivial, trivial⟩
  · rw [byte_write16 _ _ _ (by omega) (by omega)]
    by_cases h : off ≤ k ∧ k < off + 16
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx, XBinOp.eval]
      rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega), Offset.add_add, Nat.add_sub_cancel' h.1]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr]

/-! ## The 16 bytes of keystream of a register -/

theorem outReg_ne6 : ∀ l, l < 4 → outReg l ≠ .xmm6 := by decide

/-- Byte `k % 64` of a serialized state, in row `r`. -/
theorem serialize_row (S : CState) {k r : Nat} (hk : k % 64 / 16 = r) :
    (serialize S).getD (k % 64) 0 =
      (S[4 * r + k % 16 / 4]'(by omega)).extractLsb' (8 * (k % 16 % 4)) 8 := by
  rw [serialize_getD _ (Nat.mod_lt _ (by decide)), getElem_congr_idx (show k % 64 / 4 = 4 * r + k % 16 / 4 by omega),
    show k % 64 % 4 = k % 16 % 4 by omega]

/-- Byte `k` of the keystream of the four blocks `B`. -/
abbrev ksb (B : Nat → CState) (k : Nat) : Byte := (serialize (B (k / 64))).getD (k % 64) 0

/-- Byte `t` of a register holding row `r` of block `l` is byte `64 l + 16 r + t` of the keystream. -/
theorem reg_byte {B : Nat → CState} {r l : Nat} (hr : r < 4) {v : BitVec 128}
    (hv : ∀ j (hj : j < 4), dword v j = (B l)[4 * r + j]'(by omega)) {t : Nat} (ht : t < 16) :
    v.extractLsb' (8 * t) 8 = ksb B (64 * l + 16 * r + t) := by
  have e₁ : (64 * l + 16 * r + t) / 64 = l := by omega
  have e₂ : (64 * l + 16 * r + t) % 64 / 16 = r := by omega
  have e₃ : (64 * l + 16 * r + t) % 16 = t := by omega
  rw [ksb, e₁, serialize_row _ e₂]
  simp only [e₃]
  rw [byte_dword, hv _ (by omega)]

/-! ## A chunk of 16 bytes -/

/-- The 16 bytes of data at `k / 16` are all within the `W` bytes. -/
abbrev Full (W k : Nat) : Prop := 16 * (k / 16) + 16 ≤ W

/-- Where the 16 bytes that run past the end of the data start, if any. -/
abbrev sOff (W : Nat) : Nat := W / 16 * 16

/-- The keystream for the bytes past the last 16-byte boundary of the data,
if there are any and the 16 bytes from that boundary are `done`, is in
`buf[0, 16)`. -/
def Stashed (buf : Addr) (B : Nat → CState) (W : Nat) (done : Nat → Prop) (m : Mem) : Prop :=
  W % 16 ≠ 0 → done (sOff W) → ∀ i, i < W % 16 → m (buf + BitVec.ofNat 64 i) = ksb B (sOff W + i)

/-- While XORing row `r` of the four blocks `B` into `W` bytes of data: the
blocks below `l` are done, the registers `outReg l'` hold row `r` of the
blocks, and only the data and `buf[0, 16)` have been written since `s₁`. -/
structure XO (a buf : Addr) (B : Nat → CState) (W r l : Nat) (s₁ s : State) : Prop where
  data : ∀ k, k < W → s.mem (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 = r ∧ k / 64 < l ∧ Full W k then
      s₁.mem (a + BitVec.ofNat 64 k) ^^^ ksb B k
    else s₁.mem (a + BitVec.ofNat 64 k)
  stash : Stashed buf B W (fun o => o % 64 / 16 < r ∨ (o % 64 / 16 = r ∧ o / 64 < l)) s.mem
  regs : ∀ l', l' < 4 → ∀ j (hj : j < 4) (hr : r < 4), dword (s.xmm (outReg l')) j = (B l')[4 * r + j]
  frame : Frame [dW a W, stashR buf] s₁.mem s.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section Chunk
variable {a buf : Addr} {B : Nat → CState} {W n : Nat} (hn : n < 2 ^ 32) (hW : W = min n 256)
  {s₁ : State} (hd : DCtx a W s₁) (hbe : s₁.ea (at_ .edi 0) = buf + BitVec.ofNat 64 0)
  (hwb : bufR buf ∈ s₁.wr) (hdb : (dW a W).Disjoint (stashR buf))
  (hebp : s₁.gpr .ebp = BitVec.ofNat 32 n)
include hn hW hd hbe hwb hdb hebp

omit hn hW hd hbe hwb hebp in
/-- The bytes of `buf[0, 16)` are outside the data. -/
theorem stash_out {i : Nat} (hi : i < 16) : ∀ r ∈ [dW a W], ¬ r.Contains (buf + BitVec.ofNat 64 i) 1 := by
  intro r hr hc
  simp only [List.mem_singleton] at hr; subst hr
  exact hdb _ hc (Offset.contains_base buf (by omega) (by lit_omega))

theorem chunk_ok {r l : Nat} (hr : r < 4) (hl : l < 4) {s : State} (h : XO a buf B W r l s₁ s) :
    WP isa (chunk (outReg l) (chunkOff r l)) s (XO a buf B W r (l + 1) s₁) := by
  have hW256 : W ≤ 256 := by omega
  have hgb : s.gpr .ebp = BitVec.ofNat 32 n := by rw [h.gpr, hebp]
  have ho : chunkOff r l + 16 ≤ 256 := by simp only [chunkOff]; omega
  have hreg := h.regs l hl
  unfold chunk
  refine WP.seq (WP.mono (cmpi_ok s .ebp _) fun s₂ ⟨g₂, m₂, x₂, r₂, w₂, c₂⟩ => ?_)
  rw [hgb, toNat_ofNat32 hn, toNat_ofNat32 (by omega)] at c₂
  refine WP.ite (decide (n < chunkOff r l + 16)) (by simp only [eval, c₂]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine WP.seq (WP.mono (cmpi_ok s₂ .ebp _) fun s₃ ⟨g₃, m₃, x₃, r₃, w₃, c₃⟩ => ?_)
    rw [g₂, hgb, toNat_ofNat32 hn, toNat_ofNat32 (by omega)] at c₃
    refine WP.ite (decide (n < chunkOff r l + 1)) (by simp only [eval, c₃]) (fun hle => ?_) (fun hgt => ?_)
    · -- Past the end of the data: nothing.
      simp only [decide_eq_true_eq] at hle
      refine WP.block_nil ⟨fun k hk => ?_, fun hz hdn i hi => ?_, fun l' hl' j hj hr' => ?_, ?_, ?_, ?_, ?_⟩
      · rw [m₃, m₂, h.data k hk]
        by_cases c : k % 64 / 16 = r ∧ k / 64 < l ∧ Full W k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega, c.2.2⟩]
        · rw [ite_eq_right c, ite_eq_right (by simp only [Full, chunkOff] at *; omega)]
      · rw [m₃, m₂]
        exact h.stash hz (by simp only [sOff, chunkOff] at *; omega) i hi
      · rw [x₃, x₂]; exact h.regs l' hl' j hj hr'
      · rw [m₃, m₂]; exact h.frame
      · rw [g₃, g₂, h.gpr]
      · rw [r₃, r₂, h.rd]
      · rw [w₃, w₂, h.wr]
    · -- The last bytes of the data: the 16 bytes of keystream into `buf[0, 16)`.
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hgt
      have hWn : W = n := by simp only [chunkOff] at *; omega
      have e : s₃.ea (at_ .edi 0) = buf + BitVec.ofNat 64 0 := by
        rw [ea_gpr g₃, ea_gpr g₂, ea_gpr h.gpr, hbe]
      have o : InRegions s₃.wr (buf + BitVec.ofNat 64 0) 16 := by
        rw [w₃, w₂, h.wr]; exact out_buf hwb (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, e, o, ite_true,
        Option.some.injEq, exists_eq_left']
      have hm : ∀ k, k < W → (s₃.mem.writeW (buf + BitVec.ofNat 64 0) (s₃.xmm (outReg l)))
          (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) := by
        intro k hk
        rw [writeW_byte_off _ _ _ _ ?_, m₃, m₂]
        have hc : (dW a W).Contains (a + BitVec.ofNat 64 k) 1 := Offset.contains_base a (by omega) (by lit_omega)
        by_contra hlt'
        rw [BitVec.add_zero] at hlt'
        exact hdb _ hc (by simp only [Region.Contains]; omega)
      refine ⟨fun k hk => ?_, fun hz _ i hi => ?_, fun l' hl' j hj hr' => ?_, ?_, ?_, ?_, ?_⟩
      · show (s₃.mem.writeW _ _) _ = _
        rw [hm k hk, h.data k hk]
        by_cases c : k % 64 / 16 = r ∧ k / 64 < l ∧ Full W k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega, c.2.2⟩]
        · rw [ite_eq_right c, ite_eq_right (by simp only [Full, chunkOff] at *; omega)]
      · show (s₃.mem.writeW _ _) _ = _
        have hs : sOff W = chunkOff r l := by simp only [sOff, chunkOff] at *; omega
        rw [show buf + BitVec.ofNat 64 i = buf + BitVec.ofNat 64 0 + BitVec.ofNat 64 i by
            rw [Offset.add_add, Nat.zero_add], writeW_byte _ _ _ (by omega) (by lit_omega), hs, x₃, x₂]
        exact reg_byte hr (fun j hj => hreg j hj hr) (by omega)
      · show dword (s₃.xmm (outReg l')) j = _
        rw [x₃, x₂]; exact h.regs l' hl' j hj hr'
      · show Frame _ _ (s₃.mem.writeW _ _)
        rw [m₃, m₂]
        exact h.frame.trans ((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
          (Offset.contains_base buf (by decide) (by decide)))
      · show s₃.gpr = _; rw [g₃, g₂, h.gpr]
      · show s₃.rd = _; rw [r₃, r₂, h.rd]
      · show s₃.wr = _; rw [w₃, w₂, h.wr]
  · -- All 16 bytes within the data: XORed.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    have hfull : chunkOff r l + 16 ≤ W := by omega
    refine WP.mono (xor16_ok (outReg_ne6 l hl) hW256 hfull ((hd.of h.gpr h.wr).of g₂ w₂))
      fun s' ⟨hm, hf, hx, hg, hrd, hwr⟩ => ⟨fun k hk => ?_, fun hz hdn i hi => ?_,
        fun l' hl' j hj hr' => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm k hk, m₂, h.data k hk]
      by_cases hin : chunkOff r l ≤ k ∧ k < chunkOff r l + 16
      · have c₁ : ¬ (k % 64 / 16 = r ∧ k / 64 < l ∧ Full W k) := by simp only [chunkOff] at hin; omega
        have c₂ : k % 64 / 16 = r ∧ k / 64 < l + 1 ∧ Full W k := by simp only [Full, chunkOff] at *; omega
        rw [ite_eq_left hin, ite_eq_right c₁, ite_eq_left c₂, x₂,
          show k = chunkOff r l + (k - chunkOff r l) by omega, Nat.add_sub_cancel_left,
          reg_byte hr (fun j hj => hreg j hj hr) (by omega)]
        simp only [chunkOff]
      · rw [ite_eq_right hin]
        by_cases c : k % 64 / 16 = r ∧ k / 64 < l ∧ Full W k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega, c.2.2⟩]
        · rw [ite_eq_right c, ite_eq_right (by simp only [chunkOff] at hin; omega)]
    · rw [hf _ (stash_out hdb (by omega)), m₂]
      exact h.stash hz (by simp only [sOff, chunkOff] at *; omega) i hi
    · rw [hx _ (outReg_ne6 l' hl'), x₂]; exact h.regs l' hl' j hj hr'
    · exact h.frame.trans ((m₂ ▸ hf).mono (by simp))
    · rw [hg, g₂, h.gpr]
    · rw [hrd, r₂, h.rd]
    · rw [hwr, w₂, h.wr]

end Chunk

/-! ## The whole output -/

/-- Block `l` of the four: the rounds' result `vs l` plus the input state `ctr C l`. -/
abbrev blk (vs : Nat → CState) (C : CState) (l : Nat) : CState :=
  Vector.zipWith (· + ·) (vs l) (ctr C l)

/-- After rows below `r`: those rows of the four blocks are XORed into the
data, but for the 16 bytes past its end, if any, which are in `buf[0, 16)`;
only the data and `buf[0, 16)` have been written since `s₀`. -/
structure FI (a buf : Addr) (B : Nat → CState) (W r : Nat) (s₀ s : State) : Prop where
  data : ∀ k, k < W → s.mem (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 < r ∧ Full W k then s₀.mem (a + BitVec.ofNat 64 k) ^^^ ksb B k
    else s₀.mem (a + BitVec.ofNat 64 k)
  stash : Stashed buf B W (fun o => o % 64 / 16 < r) s.mem
  frame : Frame [dW a W, stashR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem FI.zero (a buf : Addr) (B : Nat → CState) (W : Nat) (s₀ : State) : FI a buf B W 0 s₀ s₀ :=
  ⟨fun k _ => by rw [ite_eq_right (by omega)], fun _ h => absurd h (Nat.not_lt_zero _),
    Frame.refl _ _, rfl, rfl, rfl⟩

section
variable {st buf a : Addr} {vs : Nat → CState} {C : CState} {W n : Nat} {s₀ : State}
  (hc : Ctx st buf s₀) (hd : DCtx a W s₀) (hn : n < 2 ^ 32) (hW : W = min n 256)
  (hebp : s₀.gpr .ebp = BitVec.ofNat 32 n) (db : (dW a W).Disjoint (bufR buf))
  (ds : (dW a W).Disjoint (stR st))
include hc hd hn hW hebp db ds

omit ds in
theorem finishRow_ok {r : Nat} (hr : r < 4) {s : State} (h : FI a buf (blk vs C) W r s₀ s)
    (hh : RowHolds buf vs r s.mem) (hct : Ctrs buf C 4 s.mem) (hC : stateAt s.mem st = C) :
    WP isa (finishRow r) s (FI a buf (blk vs C) W (r + 1) s₀) := by
  have hcs := hc.of h.gpr h.wr
  have hdb : (dW a W).Disjoint (stashR buf) := db.sub_right (Region.sub_prefix (by decide))
  rw [finishRow]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadRow_ok hr hcs hh) fun s₁ ⟨hreg, hrow, hm₁, hg₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  have aw₀ : AW vs C r 0 s₁ s₁ :=
    ⟨fun j hj _ l hl => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hreg j hj l hl,
      by rw [hC] at hrow; exact hrow, rfl, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => AW vs C r i s₁ s)
    (fun i s hi hs => addWord_ok hr hi (hcs.of hg₁ hwr₁) (hm₁ ▸ hct) hs) 4 (Nat.le_refl _) s₁ aw₀)
    fun s₂ h₂ => ?_
  refine WP.mono (transpose_ok s₂) fun s₃ ⟨ht, hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have hm : s₃.mem = s.mem := by rw [hm₃, h₂.mem, hm₁]
  have hg : s₃.gpr = s₀.gpr := by rw [hg₃, h₂.gpr, hg₁, h.gpr]
  have hw : s₃.wr = s₀.wr := by rw [hwr₃, h₂.wr, hwr₁, h.wr]
  have hd₃ : DCtx a W s₃ := hd.of hg hw
  have hbe : s₃.ea (at_ .edi 0) = buf + BitVec.ofNat 64 0 := (ea_gpr hg _).trans (hc.eaB 0 (by decide))
  have hebp₃ : s₃.gpr .ebp = BitVec.ofNat 32 n := by rw [hg, hebp]
  have hwb₃ : bufR buf ∈ s₃.wr := hw ▸ hc.wb
  have xo₀ : XO a buf (blk vs C) W r 0 s₃ s₃ :=
    ⟨fun k _ => by rw [ite_eq_right (by omega)],
      fun hz hdn i hi => by rw [hm]; exact h.stash hz (by omega) i hi,
      fun l' hl' j hj hr' => by rw [ht l' hl' j hj, h₂.regs j hj hr' l' hl', ite_eq_left hj, Vector.getElem_zipWith],
      Frame.refl _ _, rfl, rfl, rfl⟩
  have step := fun l (hl : l < 4) {s : State} (hs : XO a buf (blk vs C) W r l s₃ s) =>
    chunk_ok hn hW hd₃ hbe hwb₃ hdb hebp₃ hr hl hs
  refine WP.seq (WP.mono (step 0 (by decide) xo₀) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (step 1 (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (step 2 (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.mono (step 3 (by decide) h₆) fun s₇ h₇ => ⟨fun k hk => ?_, fun hz hdn i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₇.data k hk, hm, h.data k hk]
    by_cases c : k % 64 / 16 = r
    · by_cases cf : Full W k
      · rw [ite_eq_left ⟨c, by omega, cf⟩, ite_eq_right (by omega), ite_eq_left ⟨by omega, cf⟩]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega)]
      by_cases c' : k % 64 / 16 < r ∧ Full W k
      · rw [ite_eq_left c', ite_eq_left ⟨by omega, c'.2⟩]
      · rw [ite_eq_right c', ite_eq_right (by omega)]
  · exact h₇.stash hz (by simp only [sOff] at *; omega) i hi
  · exact h.frame.trans (hm ▸ h₇.frame)
  · rw [h₇.gpr, hg]
  · rw [h₇.rd, hrd₃, h₂.rd, hrd₁, h.rd]
  · rw [h₇.wr, hw]

omit hd hn hW hebp in
/-- Rows `r ≥ 1` still find their words, the counters and the state, which
the output has not written. -/
theorem rowPre {r : Nat} (hr : r < 4) (hr1 : 1 ≤ r) (hh : Holds4 buf vs s₀.mem) (hct : Ctrs buf C 4 s₀.mem)
    (hC : stateAt s₀.mem st = C) {s : State} (h : FI a buf (blk vs C) W r s₀ s) :
    RowHolds buf vs r s.mem ∧ Ctrs buf C 4 s.mem ∧ stateAt s.mem st = C := by
  have hs : ∀ d, 16 ≤ d → d + 4 ≤ 320 → ∀ r' ∈ [dW a W, stashR buf],
      (⟨buf + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r' := by
    intro d h16 h320 r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (db.sub_right (Offset.sub_base buf h320)).symm
    · exact Offset.disjoint_base buf h16 (by lit_omega)
  refine ⟨fun i hi _ l hl => ?_, fun l hl => ?_, ?_⟩
  · rw [h.frame.readW (Region.contains_self _ _) (hs _ (by omega) (by omega)) (by decide)]
    exact hh _ (by omega) l hl
  · rw [h.frame.readW (Region.contains_self _ _) (hs _ (by simp only [ctrOff]; omega)
      (by simp only [ctrOff]; omega)) (by decide)]
    exact hct l hl
  · rw [stateAt_frame h.frame (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r' (rfl | rfl)
      · exact ds.symm
      · exact hc.sb.sub_right (Region.sub_prefix (by decide)))]
    exact hC

theorem finish4_ok (hh : Holds4 buf vs s₀.mem) (hct : Ctrs buf C 4 s₀.mem) (hC : stateAt s₀.mem st = C) :
    WP isa finish4 s₀ (FI a buf (blk vs C) W 4 s₀) := by
  have row := fun r (hr : r < 4) {s : State} (h : FI a buf (blk vs C) W r s₀ s)
      (p : RowHolds buf vs r s.mem ∧ Ctrs buf C 4 s.mem ∧ stateAt s.mem st = C) =>
    finishRow_ok hc hd hn hW hebp db hr h p.1 p.2.1 p.2.2
  have pre := fun r (hr : r < 4) (hr1 : 1 ≤ r) {s : State} (h : FI a buf (blk vs C) W r s₀ s) =>
    rowPre hc db ds hr hr1 hh hct hC h
  unfold finish4
  refine WP.seq (WP.mono (row 0 (by decide) (FI.zero a buf _ W s₀)
    ⟨fun i hi _ l hl => hh _ (by omega) l hl, hct, hC⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (row 1 (by decide) h₁ (pre 1 (by decide) (by decide) h₁)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (row 2 (by decide) h₂ (pre 2 (by decide) (by decide) h₂)) fun s₃ h₃ => ?_)
  exact row 3 (by decide) h₃ (pre 3 (by decide) (by decide) h₃)

end

end VG.Proof.ChaCha20.X86.Quad
