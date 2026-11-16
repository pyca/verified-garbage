module

public import VerifiedGarbage.Proof.X25519.Arm.Words.Chain
public import VerifiedGarbage.Proof.X25519.Arm.Ladder
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.Arm.Words.Mul
import VerifiedGarbage.Proof.X25519.Arm.Words.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap
import VerifiedGarbage.Proof.X25519.Arm.Invert
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the ladder's and the inversion's loops, which build in parallel with the proofs of
-- the setup and the output and are not checked again when those change.

/-!
# X25519 on 32-bit ARM with `umaal`: the ladder and the inversion

`SlotsW m B qs sm v`: each slot `q` of `qs` holds the element `v q`, as a
number below `2p` if `q` is in `sm` (what `add` and `sub` need of their
operands, and `mul` and `addA24` give). The field operations as updates of
`v` (`op_ok`, `opCswap`), between which the counter and the last bit of the
scalar are in the working space (`Cur`); one iteration of the ladder
(`step_ok`) and the loop (`ladder_ok`); and the inversion (`invert_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Impl.X25519.Arm (BITS cswapStep storeN)
open VG.Spec.X25519 (P Fe Ladder ladderStep a24)
open VG.Proof.X25519 (toFe toFe_mul toFe_add toFe_sub toFe_addA24 ladderAfter ladderAfter_step ladderStep_eq bit
  bit_le ladderAfter_swap_le)

/-! ## The slots -/

/-- What the ladder and the inversion write of the working space: `CNT`,
`SWAP`, the elements and `ACC`. -/
abbrev FAW (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 44, 532⟩

/-- Each slot `q` of `qs` is an element's, and holds `v q`, as a number below
`2p` if `q` is in `sm`. -/
def SlotsW (m : Mem) (B : Addr) (qs sm : List Nat) (v : Nat → Fe) : Prop :=
  ∀ q ∈ qs, (64 ≤ q ∧ q + 32 ≤ ACC) ∧ toFe (W m B q) = v q ∧ (q ∈ sm → W m B q < 2 * P)

theorem SlotsW.mono {m : Mem} {B : Addr} {qs qs' sm sm' : List Nat} {v : Nat → Fe} (h : SlotsW m B qs sm v)
    (hs : ∀ q ∈ qs', q ∈ qs) (hm : ∀ q ∈ qs', q ∈ sm' → q ∈ sm) : SlotsW m B qs' sm' v := fun q hq =>
  ⟨(h q (hs q hq)).1, (h q (hs q hq)).2.1, fun h' => (h q (hs q hq)).2.2 (hm q hq h')⟩

theorem SlotsW.congr {m : Mem} {B : Addr} {qs sm : List Nat} {v w : Nat → Fe} (h : SlotsW m B qs sm v)
    (hs : ∀ q ∈ qs, v q = w q) : SlotsW m B qs sm w := fun q hq =>
  ⟨(h q hq).1, (h q hq).2.1.trans (hs q hq), (h q hq).2.2⟩

/-- The slots in a frame apart from them. -/
theorem SlotsW.frame {m m' : Mem} {B : Addr} {qs sm : List Nat} {v : Nat → Fe} (h : SlotsW m B qs sm v)
    {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, ∀ q ∈ qs, 64 ≤ q → q + 32 ≤ ACC → ∀ k < 8,
      (⟨B + BitVec.ofNat 64 (q + 4 * k), 4⟩ : Region).Disjoint r) : SlotsW m' B qs sm v := fun q hq => by
  obtain ⟨hb, hv, hs⟩ := h q hq
  have e := W_frame hf (o := q) fun r hr k hk => hd r hr q hq hb.1 hb.2 k hk
  exact ⟨hb, by rw [e]; exact hv, fun h' => by rw [e]; exact hs h'⟩

/-- The slots after a write of `CNT` or `SWAP`. -/
theorem SlotsW.low {m m' : Mem} {B : Addr} {qs sm : List Nat} {v : Nat → Fe} (h : SlotsW m B qs sm v)
    (hf : Frame [⟨B + BitVec.ofNat 64 44, 8⟩] m m') : SlotsW m' B qs sm v :=
  h.frame hf fun r hr q _ h1 h2 k hk => by
    have hA : ACC = 544 := rfl
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_using [h1])) (by omega_using [h2, hA, hk]) (by omega_arith)

theorem cell_frame {B : Addr} (m : Mem) {d : Nat} (hd : 44 ≤ d ∧ d + 4 ≤ 52) (x : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 44, 8⟩] m (m.writeW (B + BitVec.ofNat 64 d) x) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by omega_using [hd]) (by omega_using [hd]) (by omega_arith))

theorem low_FAW {b : BitVec 32} {m m' : Mem} (hf : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] m m') :
    Frame [FAW b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩

/-- The bits of the scalar stay where the code below them writes. -/
theorem Bits.frame' {b : BitVec 32} {k : Nat} {m m' : Mem} (h : Bits b k m) {e n : Nat}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 e, n⟩] m m') (he : e + n ≤ BITS) : Bits b k m' := fun t ht => by
  have hB : BITS = 1280 := rfl
  rw [hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact fun hc => Offset.disjoint (State.addr b) (d := BITS + t) (n := 1) (e := e) (k := n)
      (.inr (by omega_using [he])) (by omega_using [hB, ht]) (by omega_using [he, hB]) _
      (Region.contains_self _ _) hc]
  exact h t ht

theorem Bits.frame {b : BitVec 32} {k : Nat} {m m' : Mem} (h : Bits b k m) (hf : Frame [FAW b] m m') :
    Bits b k m' := Bits.frame' h hf (by decide)

/-- Every slot of `qs` is `o` or apart from it. -/
def SepW (o : Nat) (qs : List Nat) : Bool := qs.all fun q => q == o || q + 32 ≤ o || o + 32 ≤ q

theorem sep_get {o : Nat} {qs : List Nat} (h : SepW o qs = true) {q : Nat} (hq : q ∈ qs) :
    q = o ∨ q + 32 ≤ o ∨ o + 32 ≤ q := by
  have := List.all_eq_true.mp h q hq
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this.elim (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h))

/-- Between field operations, from `s0`: the counter `c` and the bit `w` in
the working space, and the slots `qs` the elements `v`. -/
structure Cur (b : BitVec 32) (s0 : State) (c w : Nat) (qs sm : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : Ctx b s
  kp : Kp s0 s
  frame : Frame [FAW b] s0.mem s.mem
  cnt : wd s.mem (State.addr b) CNT = c
  swp : wd s.mem (State.addr b) SWAP = w
  slots : SlotsW s.mem (State.addr b) qs sm v

section
variable {b : BitVec 32} {s0 : State} {c w : Nat} {qs sm : List Nat} {v : Nat → Fe}

theorem Cur.congr {s : State} {qs' sm' : List Nat} {v' : Nat → Fe} (h : Cur b s0 c w qs sm v s)
    (hq : ∀ q ∈ qs', q ∈ qs) (hm : ∀ q ∈ qs', q ∈ sm' → q ∈ sm) (hv : ∀ q ∈ qs', v q = v' q) :
    Cur b s0 c w qs' sm' v' s :=
  ⟨h.ctx, h.kp, h.frame, h.cnt, h.swp, (h.slots.mono hq hm).congr hv⟩

/-- After an operation that writes the slot `o` (and `ACC`). -/
theorem Cur.next {o : Nat} (hq : SepW o qs = true) (ho : 64 ≤ o ∧ o + 32 ≤ ACC) {s s' : State}
    (h : Cur b s0 c w qs sm v s) (hk : Kp s s')
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 32⟩] s.mem s'.mem)
    {x : Fe} (hx : toFe (W s'.mem (State.addr b) o) = x) {sm' : List Nat} (hsm : ∀ q ∈ sm', q ≠ o → q ∈ sm)
    (hsmall : o ∈ sm' → W s'.mem (State.addr b) o < 2 * P) : Cur b s0 c w (o :: qs) sm' (upd v o x) s' := by
  have hA : ACC = 544 := rfl
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  have hw : ∀ d, d + 4 ≤ 64 → wd s'.mem (State.addr b) d = wd s.mem (State.addr b) d := fun d hd =>
    wd_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact Offset.disjoint _ (.inl (by omega_using [hd, ho, hA])) (by omega_using [hd]) (by omega_using [ho, hA])
  refine ⟨hk.ctx h.ctx, h.kp.trans hk, h.frame.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩),
    by rw [hw _ (by omega_using [hC])]; exact h.cnt, by rw [hw _ (by omega_using [hS])]; exact h.swp,
    fun q hq' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_using [ho, hA]) (by omega_using [ho, hA])
  · by_cases hqo : q = o
    · subst hqo; exact ⟨ho, by rw [upd_self]; exact hx, hsmall⟩
    · have hq'' := (List.mem_cons.mp hq').resolve_left hqo
      obtain ⟨hb, hv, hs⟩ := h.slots q hq''
      have hsep := sep_get hq hq''
      have e : W s'.mem (State.addr b) q = W s.mem (State.addr b) q := W_frame hf fun r hr k hk' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega_using [hsep, hqo, hk']) (by omega_using [hb, hA, hk'])
            (by omega_using [ho, hA])
        · exact Offset.disjoint _ (.inl (by omega_using [hb, hk'])) (by omega_using [hb, hA, hk'])
            (by omega_using [hA])
      exact ⟨hb, by rw [upd_of_ne _ _ hqo, e]; exact hv, fun h' => by rw [e]; exact hs (hsm q h' hqo)⟩

end

/-! ## Field operations -/

/-- A field operation: `o = x · y`, `x + y`, `x - y` or `x + a24 · y`. -/
inductive FOp
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)
  | a24 (o x y : Nat)

def FOp.code : FOp → List Instr
  | .mul o x y => Impl.X25519.Arm.Words.mul o x y
  | .add o x y => Impl.X25519.Arm.Words.add o x y
  | .sub o x y => Impl.X25519.Arm.Words.sub o x y
  | .a24 o x y => addA24 o x y

def FOp.out : FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .a24 o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .add _ x _ | .sub _ x _ | .a24 _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y | .a24 _ _ y => y

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y
  | .a24 _ x y, v => v x + Spec.X25519.a24 * v y

/-- The operands that must be below `2p` are. -/
def FOp.needs : FOp → List Nat → Bool
  | .mul .., _ | .a24 .., _ => true
  | .add _ x y, sm => sm.contains x && sm.contains y
  | .sub _ _ y, sm => sm.contains y

/-- The slots below `2p` after the operation. -/
def FOp.sm : FOp → List Nat → List Nat
  | .mul o _ _, sm | .a24 o _ _, sm => o :: sm
  | .add o _ _, sm | .sub o _ _, sm => sm.filter (· != o)

section
variable {b : BitVec 32} {s0 : State} {c w : Nat} {qs sm : List Nat} {v : Nat → Fe}

theorem not_mem_filter_ne {o : Nat} {l : List Nat} (h : o ∈ l.filter (· != o)) : False := by
  have := (List.mem_filter.mp h).2
  simp at this

theorem op_ok (op : FOp) (hq : SepW op.out qs = true) (ho : 64 ≤ op.out ∧ op.out + 32 ≤ ACC) (hx : op.x ∈ qs)
    (hy : op.y ∈ qs) (hn : op.needs sm = true) {s : State} (h : Cur b s0 c w qs sm v s) :
    WP isa (.block op.code) s (Cur b s0 c w (op.out :: qs) (op.sm sm) (upd v op.out (op.val v))) := by
  have hA : ACC = 544 := rfl
  cases op with
  | mul o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    show WP isa (.block (Impl.X25519.Arm.Words.mul o x y)) s (Cur b s0 c w (o :: qs) (o :: sm) (upd v o (v x * v y)))
    exact WP.mono (mul_ok (o := o) (by omega_using [ho', hA]) hbx.2 hby.2 h.ctx) fun s' ⟨hk, hf, hv, hl⟩ =>
      h.next hq ho' hk hf (by rw [← hvx, ← hvy]; exact toFe_mul hv)
        (fun q hq' hne => (List.mem_cons.mp hq').resolve_left hne) (fun _ => hl)
  | add o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    have hn' : (sm.contains x && sm.contains y) = true := hn
    simp only [Bool.and_eq_true, List.contains_iff_mem] at hn'
    show WP isa (.block (Impl.X25519.Arm.Words.add o x y)) s
      (Cur b s0 c w (o :: qs) (sm.filter (· != o)) (upd v o (v x + v y)))
    exact WP.mono (add_ok (o := o) (by omega_using [ho', hA]) (by omega_using [hbx, hA]) (by omega_using [hby, hA])
      h.ctx (hsx hn'.1) (hsy hn'.2)) fun s' ⟨hk, hf, hv⟩ =>
      h.next hq ho' hk (hf.mono fun r hr => by simp [List.mem_singleton.mp hr])
        (by rw [← hvx, ← hvy]; exact toFe_add hv) (fun q hq' _ => (List.mem_filter.mp hq').1)
        (fun h' => (not_mem_filter_ne h').elim)
  | sub o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    have hn' : sm.contains y = true := hn
    simp only [List.contains_iff_mem] at hn'
    show WP isa (.block (Impl.X25519.Arm.Words.sub o x y)) s
      (Cur b s0 c w (o :: qs) (sm.filter (· != o)) (upd v o (v x - v y)))
    exact WP.mono (sub_ok (o := o) (by omega_using [ho', hA]) (by omega_using [hbx, hA]) (by omega_using [hby, hA])
      h.ctx (hsy hn')) fun s' ⟨hk, hf, hv⟩ =>
      h.next hq ho' hk (hf.mono fun r hr => by simp [List.mem_singleton.mp hr])
        (by rw [← hvx, ← hvy]; exact toFe_sub hv) (fun q hq' _ => (List.mem_filter.mp hq').1)
        (fun h' => (not_mem_filter_ne h').elim)
  | a24 o x y =>
    have hq : SepW o qs = true := hq
    have hx : x ∈ qs := hx
    have hy : y ∈ qs := hy
    obtain ⟨hbx, hvx, hsx⟩ := h.slots _ hx
    obtain ⟨hby, hvy, hsy⟩ := h.slots _ hy
    have ho' : 64 ≤ o ∧ o + 32 ≤ ACC := ho
    show WP isa (.block (addA24 o x y)) s (Cur b s0 c w (o :: qs) (o :: sm) (upd v o (v x + Spec.X25519.a24 * v y)))
    exact WP.mono (addA24_ok (o := o) (by omega_using [ho', hA]) (by omega_using [hbx, hA])
      (by omega_using [hby, hA]) h.ctx) fun s' ⟨hk, hf, hv, hl⟩ =>
      h.next hq ho' hk (hf.mono fun r hr => by simp [List.mem_singleton.mp hr])
        (by rw [← hvx, ← hvy]; exact toFe_addA24 hv) (fun q hq' hne => (List.mem_cons.mp hq').resolve_left hne)
        (fun _ => hl)

/-! ## Sequences of field operations -/

/-- The operations `ops`, then `k`. -/
def opsCode : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq (.block op.code) (opsCode ops k)

/-- Each operation's slots are separate or equal, the elements' own, and its
inputs known, and below `2p` where it needs that. -/
def opsOk : List FOp → List Nat → List Nat → Bool
  | [], _, _ => true
  | op :: ops, qs, sm => SepW op.out qs && 64 ≤ op.out && op.out + 32 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && op.needs sm && opsOk ops (op.out :: qs) (op.sm sm)

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

/-- The slots below `2p` after the operations. -/
def outsS : List FOp → List Nat → List Nat
  | [], sm => sm
  | op :: ops, sm => outsS ops (op.sm sm)

theorem ops_ok {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs sm : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs sm = true →
      Cur b s0 c w qs sm v s →
      (∀ s', Cur b s0 c w (outsQ ops qs) (outsS ops sm) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode ops k) s Q
  | [], _, _, _, s, _, h, hk => hk s h
  | op :: ops, qs, sm, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hok
    exact WP.seq (WP.mono (op_ok op h1 ⟨h2, h3⟩ h4 h5 h6 h) fun s' h' => ops_ok ops _ _ _ s' h7 h' hk)

/-! ## The conditional swap -/

theorem sel_lt {sw x y n : Nat} (hx : x < n) (hy : y < n) : sel sw x y < n := by
  unfold sel; split <;> with_reducible assumption

theorem toFe_sel (sw x y : Nat) : toFe (sel sw x y) = sel sw (toFe x) (toFe y) := by
  unfold sel; split <;> rfl

theorem opCswap {x y : Nat} (hqx : SepW x qs = true) (hqy : SepW y qs = true) (hx : x ∈ qs) (hy : y ∈ qs)
    (hxy : x + 32 ≤ y ∨ y + 32 ≤ x) (hsx : x ∈ sm) (hsy : y ∈ sm) {s : State} (h : Cur b s0 c w qs sm v s)
    {sw : Nat} (hsw : sw ≤ 1) (h9 : s.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      Cur b s0 c w qs sm (swapV x y sw v) s' ∧ s'.gpr .r9 = s.gpr .r9 := by
  have hA : ACC = 544 := rfl
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  obtain ⟨hbx, hvx, hlx⟩ := h.slots _ hx
  obtain ⟨hby, hvy, hly⟩ := h.slots _ hy
  refine WP.mono (cswapN_ok (n := 8) (b := b) (by omega_using [hbx, hA]) (by omega_using [hby, hA]) hxy h.ctx
    hsw h9) fun s' hs => ?_
  have hf : Frame [⟨State.addr b + BitVec.ofNat 64 x, 32⟩, ⟨State.addr b + BitVec.ofNat 64 y, 32⟩] s.mem s'.mem :=
    hs.frame
  have ex : W s'.mem (State.addr b) x = sel sw (W s.mem (State.addr b) x) (W s.mem (State.addr b) y) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · exact val32_congr fun k hk => (hs.lx k hk).trans rfl
    · exact val32_congr fun k hk => (hs.lx k hk).trans rfl
  have ey : W s'.mem (State.addr b) y = sel sw (W s.mem (State.addr b) y) (W s.mem (State.addr b) x) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · exact val32_congr fun k hk => (hs.ly k hk).trans rfl
    · exact val32_congr fun k hk => (hs.ly k hk).trans rfl
  have hw : ∀ d, d + 4 ≤ 64 → wd s'.mem (State.addr b) d = wd s.mem (State.addr b) d := fun d hd =>
    wd_frame hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inl (by omega_using [hd, hbx])) (by omega_using [hd]) (by omega_using [hbx, hA])
      · exact Offset.disjoint _ (.inl (by omega_using [hd, hby])) (by omega_using [hd]) (by omega_using [hby, hA])
  have hk : Kp s s' := Kp.of_rest hs.rest (by decide)
  refine ⟨⟨hk.ctx h.ctx, h.kp.trans hk, h.frame.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩),
    by rw [hw _ (by omega_using [hC])]; exact h.cnt, by rw [hw _ (by omega_using [hS])]; exact h.swp,
    fun q hq => ?_⟩, hs.rest.gpr _ (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub _ (by omega_using [hbx]) (by omega_using [hbx, hA])
    · exact Offset.sub _ (by omega_using [hby]) (by omega_using [hby, hA])
  · by_cases hnx : q = x
    · subst hnx
      refine ⟨hbx, ?_, fun _ => by rw [ex]; exact sel_lt (hlx hsx) (hly hsy)⟩
      simp only [swapV, ite_true]
      rw [ex, toFe_sel, hvx, hvy]
    by_cases hny : q = y
    · subst hny
      refine ⟨hby, ?_, fun _ => by rw [ey]; exact sel_lt (hly hsy) (hlx hsx)⟩
      simp only [swapV, hnx, ite_false, ite_true]
      rw [ey, toFe_sel, hvx, hvy]
    · obtain ⟨hb, hv, hl⟩ := h.slots q hq
      have h1 := sep_get hqx hq
      have h2 := sep_get hqy hq
      have e : W s'.mem (State.addr b) q = W s.mem (State.addr b) q := W_frame hf fun r hr k hk' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega_using [h1, hnx, hk']) (by omega_using [hb, hA, hk'])
            (by omega_using [hbx, hA])
        · exact Offset.disjoint _ (by omega_using [h2, hny, hk']) (by omega_using [hb, hA, hk'])
            (by omega_using [hby, hA])
      refine ⟨hb, ?_, fun h' => by rw [e]; exact hl h'⟩
      simp only [swapV, hnx, hny, ite_false]
      rw [e]; exact hv

end

/-! ## One iteration of the ladder -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .a24 Z2 AA E, .mul Z2 E Z2]

/-- The slots the ladder's state lives in, each below `2p`. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3]

theorem ladOps_ok : opsOk ladOps LQ LQ = true := by decide

theorem ladOps_q : ∀ q ∈ LQ, q ∈ outsQ ladOps LQ := by decide

theorem ladOps_s : ∀ q ∈ LQ, q ∈ outsS ladOps LQ := by decide

/-- The elements of the ladder's state `st`, and `x1`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3 else st.z3

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ LQ, runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q = ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    simp only [ladOps, runOps, FOp.out, FOp.val, upd, swapV, ladV, cswap_fst, cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, Nat.reduceEqDiff, ↓reduceIte]

theorem cmp_z {x y : BitVec 32} {m : Nat} (h : x.toNat = m) : (x - y == 0) = decide (m = y.toNat) := by
  subst h
  by_cases e : x = y
  · subst e; simp
  · have hne : x.toNat ≠ y.toNat := fun h' => e (BitVec.eq_of_toNat_eq h')
    simp only [hne, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply e
    rw [← BitVec.sub_add_cancel x y, h']
    exact BitVec.zero_add y

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : BitVec 32) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : Cur b sL n (ladderAfter k x1 n).swap LQ LQ (ladV x1 (ladderAfter k x1 n)) s

section
variable {b : BitVec 32}

/-- The counter decremented in `CNT`, and in `r1`. -/
theorem dec_ok {s0 : State} {n w : Nat} {qs sm : List Nat} {v : Nat → Fe} {s : State}
    (h : Cur b s0 n w qs sm v s) (hn : 1 ≤ n) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Cur b s0 (n - 1) w qs sm v s' → s'.gpr .r1 = BitVec.ofNat 32 (n - 1) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .r1 .r0 CNT :: .dp .sub .r1 .r1 (.imm 1) :: .str .r1 .r0 CNT :: is)) s Q := by
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  refine ldr0_ok h.ctx (d := CNT) (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have hlt : n < 2 ^ 32 := by rw [← h.cnt]; exact wd_lt _ _ _
  have e2 : s2.gpr .r1 = BitVec.ofNat 32 (n - 1) := by
    rw [u2.gpr]
    show s1.gpr .r1 - 1 = _
    rw [u1.gpr]
    have e : (s.mem.readW (State.addr b + BitVec.ofNat 64 CNT) 32).toNat = n := h.cnt
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [e]; exact hn), e, toNat_imm (by omega_using [hlt])]; rfl
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  refine str0_ok (k2.ctx h.ctx) (d := CNT) (by decide) fun s3 u3 => ?_
  have hm3 : s3.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 CNT) (BitVec.ofNat 32 (n - 1)) := by
    rw [u3.mem, e2, u2.mem, u1.mem]
  have hf3 : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s.mem s3.mem := by
    rw [hm3]; exact cell_frame _ (by omega_using [hC]) _
  have k3 : Kp s s3 := k2.trans (Kp.of_mupd u3)
  refine k s3 ⟨k3.ctx h.ctx, h.kp.trans k3, h.frame.trans (low_FAW hf3), ?_, ?_, h.slots.low hf3⟩
    (by rw [u3.gpr, e2])
  · rw [hm3, wd_write_self, toNat_imm (by omega_using [hlt])]
  · rw [hm3, wd_write_other _ _ _ (by omega_using [hC, hS]) (by omega_using [hS]) (by omega_using [hC])]
    exact h.swp

/-- The counter from `CNT`, compared with `c`. -/
theorem cnt_cmp_ok {s0 : State} {n w : Nat} {qs sm : List Nat} {v : Nat → Fe} {s : State}
    (h : Cur b s0 n w qs sm v s) {c : BitVec 32} (hc : encodable c = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Cur b s0 n w qs sm v s' → (s'.gpr .r1).toNat = n → s'.z = decide (n = c.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .r1 .r0 CNT :: .cmp .r1 (.imm c) :: is)) s Q := by
  refine ldr0_ok h.ctx (d := CNT) (by decide) fun s1 u1 => wp_cmp (op2_imm hc) fun s2 u2 hz => ?_
  have e1 : (s1.gpr .r1).toNat = n := by rw [u1.gpr]; exact h.cnt
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans ⟨by rw [u2.gpr], u2.rd, u2.wr, u2.sp⟩
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  exact k s2 ⟨k2.ctx h.ctx, h.kp.trans k2, by rw [hm2]; exact h.frame, by rw [hm2]; exact h.cnt,
    by rw [hm2]; exact h.swp, by rw [hm2]; exact h.slots⟩ (by rw [u2.gpr, e1]) (by rw [hz]; exact cmp_z e1)

theorem head_ok {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (Cur b sL (n - 1) (bit k (n - 1)) LQ LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hB : BITS = 1280 := rfl
  have hC : CNT = 44 := rfl
  have hS : SWAP = 48 := rfl
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  have hx := xor_le_one hsw hbt
  unfold stepHead
  simp only [List.cons_append, List.nil_append]
  refine dec_ok hcur hn fun s3 h3 e3 => ?_
  have hc3 := h3.ctx
  have hfit := hc3.fit
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide)
    (by rw [u4.gpr]; show State.addr (s3.gpr .r0 + s3.gpr .r1 + _) = _
        rw [e3, hc3.r0, ea2 hfit (by omega_using [hn', hB])])
    (by rw [u4.rd, u4.wr]; exact hc3.inR (by omega_using [hn', hB])) fun s5 u5 => ?_
  have e5 : s5.gpr .r2 = BitVec.ofNat 32 (bit k (n - 1)) := by
    rw [u5.gpr, u4.mem, Nat.add_comm (n - 1) BITS, Bits.frame hbits h3.frame (n - 1) (by omega_using [hn, hn'])]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, toNat_imm (by omega_using [hbt])]; omega_using [hbt]
  have k5 : Kp s3 s5 := (Kp.of_upd u4 (by decide)).trans (Kp.of_upd u5 (by decide))
  have hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  refine ldr0_ok (k5.ctx hc3) (d := SWAP) (by decide) fun s6 u6 => ?_
  have e6 : s6.gpr .r3 = BitVec.ofNat 32 (ladderAfter k x1 n).swap := by
    rw [u6.gpr, hm5]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by omega_using [hsw])]; exact h3.swp
  have k6 : Kp s3 s6 := k5.trans (Kp.of_upd u6 (by decide))
  refine str0_ok (k6.ctx hc3) (d := SWAP) (by decide) fun s7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => wp_mov (op2_imm (by decide)) fun s9 u9 =>
    wp_dp (op2_reg _ _) fun s10 u10 => ?_
  have e9 : s10.gpr .r9 = 0 - BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u10.gpr]
    show s9.gpr .r9 - s9.gpr .r2 = _
    rw [u9.gpr, u9.other _ (by decide), u8.gpr]
    show _ - (s7.gpr .r2 ^^^ s7.gpr .r3) = _
    rw [u7.gpr, e6, u6.other _ (by decide), e5, BitVec.xor_comm,
      ofNat_xor (by omega_using [hsw]) (by omega_using [hbt])]
  have hm10 : s10.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 SWAP) (BitVec.ofNat 32 (bit k (n - 1))) := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.other _ (by decide), e5, u6.mem, hm5]
  have hf10 : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s3.mem s10.mem := by
    rw [hm10]; exact cell_frame _ (by omega_using [hS]) _
  have k10 : Kp s3 s10 := k6.trans ((Kp.of_mupd u7).trans ((Kp.of_upd u8 (by decide)).trans
    ((Kp.of_upd u9 (by decide)).trans (Kp.of_upd u10 (by decide)))))
  have h10 : Cur b sL (n - 1) (bit k (n - 1)) LQ LQ (ladV x1 (ladderAfter k x1 n)) s10 := by
    refine ⟨k10.ctx hc3, h3.kp.trans k10, h3.frame.trans (low_FAW hf10), ?_, ?_, h3.slots.low hf10⟩
    · rw [hm10, wd_write_other _ _ _ (by omega_using [hC, hS]) (by omega_using [hC]) (by omega_using [hS])]
      exact h3.cnt
    · rw [hm10, wd_write_self, toNat_imm (by omega_using [hbt])]
  refine WP.append (opCswap (x := X2) (y := X3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h10 hx e9) fun s11 ⟨h11, h9'⟩ => ?_
  exact WP.mono (opCswap (x := Z2) (y := Z3) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h11 hx (by rw [h9', e9])) fun s12 h12 => h12.1

theorem step_eq :
    step = .seq (.block stepHead) (opsCode ladOps (.block [.ldr .r1 .r0 CNT, .cmp .r1 (.imm 0)])) := rfl

theorem step_ok {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_ok ladOps LQ LQ _ s1 ladOps_ok h1 fun s2 h2 => ?_)
  refine cnt_cmp_ok h2 (by decide) fun s3 h3 _ hz => WP.block_nil ⟨⟨?_⟩, hz⟩
  have e : ladderAfter k x1 (n - 1) = ladderStep k x1 (ladderAfter k x1 n) (n - 1) := by
    rw [ladderAfter_step k x1 (show n - 1 < 255 by omega_using [hn']), Nat.sub_add_cancel hn]
  refine ⟨h3.ctx, h3.kp, h3.frame, h3.cnt, ?_, ?_⟩
  · rw [h3.swp, e, ladderStep_eq]
  · refine (h3.slots.mono ladOps_q fun q hq _ => ladOps_s q hq).congr fun q hq => ?_
    rw [e]; exact ladOps_vals k x1 _ (n - 1) q hq

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsW s.mem (State.addr b) LQ LQ (ladV x1 (VG.Proof.X25519.init x1))) :
    WP isa ladder s fun s' => Kp s s' ∧ Frame [FAW b] s.mem s'.mem ∧ Ctx b s' ∧
      wd s'.mem (State.addr b) SWAP = (ladderAfter k x1 0).swap ∧
      SlotsW s'.mem (State.addr b) LQ LQ (ladV x1 (ladderAfter k x1 0)) := by
  have hC : CNT = 44 := rfl
  have hSW : SWAP = 48 := rfl
  unfold ladder
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s1 u1 => ?_)
  refine str0_ok ((Kp.of_upd u1 (by decide)).ctx hc) (d := CNT) (by decide) fun s2 u2 =>
    wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have k3 : Kp s s3 := (Kp.of_upd u1 (by decide)).trans ((Kp.of_mupd u2).trans (Kp.of_upd u3 (by decide)))
  refine str0_ok (k3.ctx hc) (d := SWAP) (by decide) fun s4 u4 => WP.block_nil ?_
  have k4 : Kp s s4 := k3.trans (Kp.of_mupd u4)
  have hm4 : s4.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 CNT) (255 : BitVec 32)).writeW
      (State.addr b + BitVec.ofNat 64 SWAP) (0 : BitVec 32) := by
    rw [u4.mem, u3.gpr, u3.mem, u2.mem, u1.gpr, u1.mem]
  have hf4 : Frame [⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s.mem s4.mem := by
    rw [hm4]
    exact (cell_frame _ (by omega_using [hC]) _).trans (cell_frame _ (by omega_using [hSW]) _)
  have hbits4 : Bits b k s4.mem := Bits.frame hbits (low_FAW hf4)
  have h255 : LadInv b k x1 s4 255 s4 := ⟨⟨k4.ctx hc, Kp.refl _, Frame.refl _ _, by
    rw [hm4, wd_write_other _ _ _ (by omega_using [hC, hSW]) (by omega_using [hC]) (by omega_using [hSW]),
      wd_write_self]; rfl, by rw [hm4, wd_write_self]; rfl, hS.low hf4⟩⟩
  refine WP.mono (Q := LadInv b k x1 s4 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ LadInv b k x1 s4 m s') ?_ 255 s4 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨k4.trans h'.kp, (low_FAW hf4).trans h'.frame, h'.ctx, h'.swp, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits4 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, hl'⟩

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

/-- `z^((p - 2) >> n)` in `R`, for `z` at `Z2`. -/
def invV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X25519.pw (v Z2) ((P - 2) >>> n))

/-- The loop invariant of the inversion from `sI`, before the step for the bit
`n - 1`. -/
structure InvInv (b : BitVec 32) (sI : State) (w : Nat) (v : Nat → Fe) (n : Nat) (s : State) : Prop where
  cur : Cur b sI n w IQ [] (invV v n) s

theorem Cur.of_fupd {s0 : State} {c w : Nat} {qs sm : List Nat} {v : Nat → Fe} {s s' : State}
    (h : Cur b s0 c w qs sm v s) (u : Fupd s s') : Cur b s0 c w qs sm v s' :=
  have k : Kp s s' := ⟨by rw [u.gpr], u.rd, u.wr, u.sp⟩
  ⟨k.ctx h.ctx, h.kp.trans k, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.cnt,
    by rw [u.mem]; exact h.swp, by rw [u.mem]; exact h.slots⟩

theorem invStep_ok {sI : State} {w : Nat} {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255)
    {s : State} (h : InvInv b sI w v n s) :
    WP isa invStep s fun s' => InvInv b sI w v (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  obtain ⟨hcur⟩ := h
  have hb := pbits (n - 1) (by omega_using [hn'])
  have he := shr_step (P - 2) (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold invStep
  refine WP.seq (dec_ok hcur hn fun s1 h1 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (op_ok (.mul R R R) (by decide) (by decide) (by decide) (by decide) rfl h1)
    fun s2 h2 => ?_)
  have h2 : Cur b sI (n - 1) w (R :: IQ) [R] (upd (invV v n) R (invV v n R * invV v n R)) s2 := h2
  -- After the square.
  have hsq : ∀ q ∈ IQ, upd (invV v n) R (invV v n R * invV v n R) q =
      upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X25519.pw_mul]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := IQ) (sm' := []) (by decide) (fun _ _ h => absurd h List.not_mem_nil) hsq
  refine WP.seq (cnt_cmp_ok h2' (c := 4) (by decide) fun s3 h3 e3 hz3 => WP.block_nil ?_)
  have hz3' : s3.z = decide (n - 1 = 4) := hz3
  refine WP.seq (WP.mono (Q := Cur b sI (n - 1) w IQ [] (invV v (n - 1))) ?_ fun s4 h4 =>
    cnt_cmp_ok h4 (c := 0) (by decide) fun s5 h5 _ hz5 => WP.block_nil ⟨⟨h5⟩, hz5⟩)
  refine WP.ite s3.z (eval_eq _) (fun ht => WP.block_nil (h3.congr (fun q hq => hq) (fun _ _ h => h) fun q _ => ?_))
    (fun hf => ?_)
  · have h4 : n - 1 = 4 := by rw [hz3'] at ht; simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inl h4), Nat.add_zero]
    · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 4 := by rw [hz3'] at hf; simpa using hf
    refine WP.seq (wp_cmp (op2_imm (by decide)) fun s4 u4 hz4 => WP.block_nil ?_)
    have h4' := h3.of_fupd u4
    have hz4' : s4.z = decide (n - 1 = 2) := by rw [hz4]; exact cmp_z e3
    refine WP.ite s4.z (eval_eq _) (fun ht => WP.block_nil (h4'.congr (fun q hq => hq) (fun _ _ h => h) fun q _ => ?_))
      (fun hf => ?_)
    · have h2 : n - 1 = 2 := by rw [hz4'] at ht; simpa using ht
      by_cases hq : q = R
      · subst hq; rw [upd_self, invV, upd_self, he, hb, iteT (.inr h2), Nat.add_zero]
      · rw [upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]
    · have h2 : n - 1 ≠ 2 := by rw [hz4'] at hf; simpa using hf
      refine WP.mono (op_ok (.mul R R Z2) (by decide) (by decide) (by decide) (by decide) rfl h4')
        fun s5 h5 => ?_
      have h5 : Cur b sI (n - 1) w (R :: IQ) [R] (upd (upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n)))) R
          (upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) R *
            upd v R (VG.Proof.X25519.pw (v Z2) (2 * ((P - 2) >>> n))) Z2)) s5 := h5
      refine h5.congr (by decide) (fun _ _ h => absurd h List.not_mem_nil) fun q _ => ?_
      by_cases hq : q = R
      · subst hq
        rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), invV, upd_self, he, hb,
          iteF (show ¬ (n - 1 = 4 ∨ n - 1 = 2) by omega_using [h4, h2]), ← VG.Proof.X25519.pw_mul,
          VG.Proof.X25519.pw_one]
      · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, invV, upd_of_ne _ _ hq]

theorem val32_one : val32 (fun k => if k = 0 then 1 else 0) 8 = 1 := by decide

theorem invert_ok {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsW s.mem (State.addr b) [Z2, X2] [] v) :
    WP isa Impl.X25519.Arm.Words.invert s fun s' => Kp s s' ∧ Frame [FAW b] s.mem s'.mem ∧ Ctx b s' ∧
      SlotsW s'.mem (State.addr b) IQ [] (upd v R (VG.Proof.X25519.pw (v Z2) (P - 2))) := by
  have hR : R = 512 := rfl
  have hC : CNT = 44 := rfl
  have hA : ACC = 544 := rfl
  unfold Impl.X25519.Arm.Words.invert
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine str0_ok (k2.ctx hc) (d := R) (by decide) fun s3 u3 => ?_
  have k3 : Kp s s3 := k2.trans (Kp.of_mupd u3)
  refine WP.append (VG.Proof.X25519.Arm.stores_ok (o := R + 4) (n := 7) (by decide) (k3.ctx hc))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  have k4 : Kp s s4 := k3.trans (Kp.of_rest h4r List.not_mem_nil)
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have k5 : Kp s s5 := k4.trans (Kp.of_upd u5 (by decide))
  refine str0_ok (k5.ctx hc) (d := CNT) (by decide) fun s6 u6 => WP.block_nil ?_
  have k6 : Kp s s6 := k5.trans (Kp.of_mupd u6)
  have hm6 : s6.mem = s4.mem.writeW (State.addr b + BitVec.ofNat 64 CNT) (255 : BitVec 32) := by
    rw [u6.mem, u5.gpr, u5.mem]
  -- The words of `R`: 1, then zeros.
  have hwR : ∀ k < 8, wd s6.mem (State.addr b) (R + 4 * k) = if k = 0 then 1 else 0 := by
    intro k hk
    rw [hm6, wd_write_other _ _ _ (by omega_using [hR, hC]) (by omega_using [hR, hk]) (by omega_using [hC])]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  have hf6 : Frame [⟨State.addr b + BitVec.ofNat 64 R, 32⟩, ⟨State.addr b + BitVec.ofNat 64 44, 8⟩] s.mem s6.mem := by
    rw [hm6, ← hm2]
    refine ((((Frame.refl _ _).writeW (List.mem_cons_self ..) (s2.gpr .r1)
      (Offset.contains (State.addr b) (d := R) (n := 4) (e := R) (k := 32) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains (State.addr b) (d := CNT) (n := 4) (e := 44) (k := 8) (by decide) (by decide) (by decide)))
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hfa : Frame [FAW b] s.mem s6.mem := hf6.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by decide) (by decide)⟩
  have hS6 : SlotsW s6.mem (State.addr b) [Z2, X2] [] v := hS.frame hf6 fun r hr q hq h1 h2 k hk => by
    have hq' : q + 32 ≤ R := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl (by omega_using [hq', hk])) (by omega_using [h2, hA, hk]) (by omega_using [hR])
    · exact Offset.disjoint _ (.inr (by omega_using [h1])) (by omega_using [h2, hA, hk]) (by decide)
  have hI6 : SlotsW s6.mem (State.addr b) IQ [] (invV v 255) := by
    intro q hq
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · obtain ⟨h1, h2, -⟩ := hS6 Z2 (by decide)
      exact ⟨h1, by rw [invV, upd_of_ne _ _ (by decide)]; exact h2, fun h => absurd h List.not_mem_nil⟩
    · refine ⟨by decide, ?_, fun h => absurd h List.not_mem_nil⟩
      rw [W_of hwR, val32_one, invV, upd_self, p255, VG.Proof.X25519.pw_zero]
      rfl
    · obtain ⟨h1, h2, -⟩ := hS6 X2 (by decide)
      exact ⟨h1, by rw [invV, upd_of_ne _ _ (by decide)]; exact h2, fun h => absurd h List.not_mem_nil⟩
  have h255 : InvInv b s6 (wd s6.mem (State.addr b) SWAP) v 255 s6 :=
    ⟨⟨k6.ctx hc, Kp.refl _, Frame.refl _ _, by rw [hm6, wd_write_self]; rfl, rfl, hI6⟩⟩
  refine WP.mono (Q := InvInv b s6 (wd s6.mem (State.addr b) SWAP) v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ InvInv b s6 (wd s6.mem (State.addr b) SWAP) v m s') ?_ 255 s6
    ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨k6.trans h'.kp, hfa.trans h'.frame, h'.ctx, h'.slots.congr fun q _ => by
      simp only [invV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (invStep_ok h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩

end

end VG.Proof.X25519.Arm.Words
