module

public import VerifiedGarbage.Proof.Sha3.X86.Permute
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Impl.Sha3.X86.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block

meta import VerifiedGarbage.Proof.Sha3.X86.Permute
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Impl.Sha3.X86.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Block

/-!
# SHA-3 and SHAKE on x86 (32-bit): the functions of each instance

Each allocates a frame of `B` bytes (`WP.frameAlloc`), stores the callee's
arguments at its base (`ArgInv`, one word at a time: `copy_step`,
`const_step`, `buf_step`), and calls the sponge function (`WP.call`), whose
precondition holds of the arguments stored (`entry_arg`), and whose buffers,
outside the stack below `esp`, the frame and the call leave as they were.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Instances

open VG VG.X86 VG.X86.Wp VG.Impl.Sha3.X86.Instances
open VG.Spec.Sha3 (Repr bytesAt rates stateAt XofRepr Xof)
open VG.Proof.Sha3.Instances (xofSponge hashSponge xofRepr_pad xofRepr_squeeze digest_of_pad)

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 2 ^ 15 := by simp [rates] at hr; omega

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

/-! ## Addresses in and above the frame -/

/-- Offset `d` of a frame of `B` bytes below `e`. -/
theorem addr_frame {e : BitVec 32} {B d : Nat} (hB : B ≤ e.toNat) (hd : d ≤ B) :
    addr (e - BitVec.ofNat 32 B) d = e.setWidth 64 - BitVec.ofNat 64 (B - d) := by
  have h := Offset.sub_ofNat_eq e (a := B - d) (b := B) (by omega)
  rw [show B - (B - d) = d by omega] at h
  rw [addr, ← h, Taint.sub_setWidth (by omega)]

/-- Offset `B + d` of a frame of `B` bytes below `e`: offset `d` of `e`. -/
theorem addr_above {e : BitVec 32} {B d : Nat} :
    addr (e - BitVec.ofNat 32 B) (B + d) = addr e d := by
  rw [addr, addr, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The frame of `B` bytes below `e`. -/
theorem frame_base {e : BitVec 32} {B : Nat} (hB : B ≤ e.toNat) :
    (e - BitVec.ofNat 32 B).setWidth 64 = e.setWidth 64 - BitVec.ofNat 64 B :=
  Taint.sub_setWidth hB

/-! ## The arguments stored in the frame -/

/-- After the first `n` of the words `vs` were stored at the base `E` of the
frame of `B` bytes, from `u₀`, the state after its allocation. -/
structure ArgInv (B : Nat) (u₀ : State) (E : BitVec 32) (vs : List (BitVec 32)) (n : Nat)
    (u : State) : Prop where
  esp : u.gpr .esp = E
  gpr : ∀ r, r ≠ .eax → u.gpr r = u₀.gpr r
  rd : u.rd = u₀.rd
  wr : u.wr = u₀.wr
  frame : Frame [⟨E.setWidth 64, B⟩] u₀.mem u.mem
  val : ∀ i < n, u.mem.readW (addr E (4 * i)) 32 = vs.getD i 0

theorem ArgInv.start {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)}
    (he : u₀.gpr .esp = E) : ArgInv B u₀ E vs 0 u₀ :=
  ⟨he, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- What the frame's position needs: `E` below a frame of `B` bytes, below
the caller's arguments, which do not wrap. -/
structure Room (B : Nat) (E : BitVec 32) : Prop where
  fit : E.toNat + B + 4 ≤ 2 ^ 32

/-- Storing `eax` as word `n` of the frame. -/
theorem store_step {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)} {n : Nat}
    {u : State} {v : BitVec 32} (hI : ArgInv B u₀ E vs n u)
    (hfr : ⟨E.setWidth 64, B⟩ ∈ u₀.wr) (hR : Room B E) (hn : 4 * n + 4 ≤ B)
    (hv : u.gpr .eax = v) (hvn : vs.getD n 0 = v) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', ArgInv B u₀ E vs (n + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block (.store (at_ (4 * n)) .eax :: is)) u Q := by
  have hf := hR.fit
  have ha : addr E (4 * n) = E.setWidth 64 + BitVec.ofNat 64 (4 * n) :=
    addr_eq (by have := hR.fit; omega)
  have hc : (⟨E.setWidth 64, B⟩ : Region).Contains (addr E (4 * n)) 4 := by
    rw [ha]; exact Offset.contains_base _ (by omega) (by omega)
  refine wp_stm hI.esp ⟨_, by rw [hI.wr]; exact hfr, hc⟩ fun u' hu => k u' ?_
  refine ⟨by rw [hu.gpr]; exact hI.esp, fun r hr => by rw [hu.gpr]; exact hI.gpr r hr,
    by rw [hu.rd, hI.rd], by rw [hu.wr, hI.wr], ?_, fun i hi => ?_⟩
  · rw [hu.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
  · rw [hu.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep ?_ (by decide), hI.val i hi]
      rw [addr_eq (by have := hR.fit; omega), ha]
      exact Offset.sep _ (by omega) (by omega) (by omega)
    · rw [Mem.readW_writeW_self32, hv, hvn]

theorem upd_inv {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)} {n : Nat}
    {u u' : State} {v : BitVec 32} (hI : ArgInv B u₀ E vs n u) (hu : Wp.Upd u u' .eax v) :
    ArgInv B u₀ E vs n u' :=
  ⟨by rw [hu.other _ (by decide)]; exact hI.esp, fun r hr => by rw [hu.other r hr]; exact hI.gpr r hr,
    by rw [hu.rd, hI.rd], by rw [hu.wr, hI.wr], by rw [hu.mem]; exact hI.frame,
    fun i hi => by rw [hu.mem]; exact hI.val i hi⟩

/-- Argument `j` of the caller as word `n`. -/
theorem copy_step {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)} {n j : Nat}
    {u : State} (hI : ArgInv B u₀ E vs n u)
    (hfr : ⟨E.setWidth 64, B⟩ ∈ u₀.wr) (hR : Room B E) (hn : 4 * n + 4 ≤ B)
    (hj : E.toNat + B + 4 + 4 * j + 4 ≤ 2 ^ 32)
    (hin : InRegions (u₀.rd ++ u₀.wr) (addr E (B + 4 + 4 * j)) 4)
    (hvn : vs.getD n 0 = u₀.mem.readW (addr E (B + 4 + 4 * j)) 32) {is : List Instr}
    {Q : State → Prop} (k : ∀ u', ArgInv B u₀ E vs (n + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block (copy B j n ++ is)) u Q := by
  have hrd : u.rd ++ u.wr = u₀.rd ++ u₀.wr := by rw [hI.rd, hI.wr]
  refine Wp.wp_ldm hI.esp (by rw [hrd]; exact hin) fun u₁ hu => ?_
  have hm : u.mem.readW (addr E (B + 4 + 4 * j)) 32 = u₀.mem.readW (addr E (B + 4 + 4 * j)) 32 := by
    rw [addr_eq (by omega)]
    refine hI.frame.readW (r := ⟨E.setWidth 64 + BitVec.ofNat 64 (B + 4 + 4 * j), 4⟩)
      (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by omega) (by omega)
  exact store_step (upd_inv hI hu) hfr hR hn (by rw [hu.gpr, hm]) hvn k

/-- The constant `c` as word `n`. -/
theorem const_step {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)} {n c : Nat}
    {u : State} (hI : ArgInv B u₀ E vs n u)
    (hfr : ⟨E.setWidth 64, B⟩ ∈ u₀.wr) (hR : Room B E) (hn : 4 * n + 4 ≤ B)
    (hvn : vs.getD n 0 = BitVec.ofNat 32 c) {is : List Instr}
    {Q : State → Prop} (k : ∀ u', ArgInv B u₀ E vs (n + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block (const c n ++ is)) u Q :=
  Wp.wp_movi fun _ hu => store_step (upd_inv hI hu) hfr hR hn hu.gpr hvn k

/-- The address `E + d` as word `n`. -/
theorem buf_step {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)} {n d : Nat}
    {u : State} (hI : ArgInv B u₀ E vs n u)
    (hfr : ⟨E.setWidth 64, B⟩ ∈ u₀.wr) (hR : Room B E) (hn : 4 * n + 4 ≤ B)
    (hvn : vs.getD n 0 = E + BitVec.ofNat 32 d) {is : List Instr}
    {Q : State → Prop} (k : ∀ u', ArgInv B u₀ E vs (n + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block (buf d n ++ is)) u Q :=
  Wp.wp_mov fun _ hu => Wp.wp_addi fun _ hu₂ => by
    have h₁ := upd_inv hI hu
    refine store_step (upd_inv h₁ hu₂) hfr hR hn ?_ hvn k
    rw [hu₂.gpr, hu.gpr, hI.esp]

/-! ## The callee's view -/

theorem absorb_nosp : NoSp Impl.Sha3.X86.Stream.absorb := NoSp.of_all (by decide +kernel)
theorem pad_nosp : NoSp Impl.Sha3.X86.Stream.pad := NoSp.of_all (by decide +kernel)
theorem squeeze_nosp : NoSp Impl.Sha3.X86.Stream.squeeze := NoSp.of_all (by decide +kernel)
theorem absorb_stack : stackUse Impl.Sha3.X86.Stream.absorb = 12 := by decide +kernel
theorem pad_stack : stackUse Impl.Sha3.X86.Stream.pad = 12 := by decide +kernel
theorem squeeze_stack : stackUse Impl.Sha3.X86.Stream.squeeze = 12 := by decide +kernel

/-- The callee's argument `i`: word `i` of the frame. -/
theorem entry_arg {B : Nat} {u₀ : State} {E : BitVec 32} {vs : List (BitVec 32)} {n : Nat}
    {t : State} (hI : ArgInv B u₀ E vs n t) (hE : 4 ≤ E.toNat) (hR : Room B E) (hn : 4 * n ≤ B)
    {i : Nat} (hi : i < n) : arg t.callEntry i = vs.getD i 0 := by
  have := hR.fit
  rw [arg_callEntry (by rw [hI.esp]; exact hE) (by rw [hI.esp]; omega), hI.esp]
  exact hI.val i hi

theorem entry_argAddr {t : State} {E : BitVec 32} (he : t.gpr .esp = E) :
    argAddr t.callEntry 0 = E.setWidth 64 := by
  rw [argAddr_callEntry, he]; simp

theorem entry_esp {t : State} {E : BitVec 32} (he : t.gpr .esp = E) :
    t.callEntry.gpr .esp = E - 4 := by rw [State.callEntry_esp, he]

/-- The frame and the return address of the call are among the `S` bytes
below `e`, the stack the function may use. -/
theorem entry_frame {B S : Nat} {u₀ : State} {e E : BitVec 32} {vs : List (BitVec 32)} {n : Nat}
    {t : State} (hI : ArgInv B u₀ E vs n t) (hE : E = e - BitVec.ofNat 32 B)
    (hS : B + 4 ≤ S) (he : S ≤ e.toNat) :
    Frame [⟨e.setWidth 64 - BitVec.ofNat 64 S, S⟩] u₀.mem t.callEntry.mem := by
  rw [State.callEntry_mem]
  have hEb : E.setWidth 64 = e.setWidth 64 - BitVec.ofNat 64 B := by rw [hE]; exact frame_base (by omega)
  have f₁ : Frame [⟨e.setWidth 64 - BitVec.ofNat 64 S, S⟩] u₀.mem t.mem :=
    hI.frame.sub fun r hr => by
      rw [List.mem_singleton.mp hr, hEb]
      exact ⟨_, List.mem_singleton_self _, Offset.sub_below _ (by omega) (by omega)⟩
  refine f₁.writeW (List.mem_singleton_self _) _ ?_
  rw [hI.esp, hE, show e - BitVec.ofNat 32 B - 4 = e - BitVec.ofNat 32 (B + 4) by
    rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl, Taint.sub_setWidth (by omega)]
  exact Offset.contains_below _ (by omega) (by omega) (by have := e.isLt; omega)

/-- The `S` bytes below `e`, as `below`. -/
theorem stack_below {e : BitVec 32} {S : Nat} (h : S ≤ e.toNat) :
    (⟨e.setWidth 64 - BitVec.ofNat 64 S, S⟩ : Region) = below e S := by
  rw [below, Taint.sub_setWidth h]

/-- A region at `e.setWidth 64 - a` of `k` bytes, among the `S` below `e`. -/
theorem in_stack (e : BitVec 32) {a k S : Nat} (h₁ : a ≤ S) (h₂ : k ≤ a) :
    Region.Sub ⟨e.setWidth 64 - BitVec.ofNat 64 a, k⟩ ⟨e.setWidth 64 - BitVec.ofNat 64 S, S⟩ :=
  Offset.sub_below _ h₁ (by omega)

/-- The state, read from a memory that differs from `m` only in `rs`, apart from it. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 200⟩ r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hi => hf.bytes (R := ⟨p, 200⟩) hd (by show 200 ≤ 2 ^ 64; decide) hi

theorem bytesAt_frame {rs : List Region} {m m' : Mem} {p : Addr} {n : Nat} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [Spec.Sha3.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- Caller argument `j` is in the arguments' region. -/
theorem arg_in {s : State} {j m : Nat} (hj : 4 * j + 4 ≤ m) (hfit : (s.gpr .esp).toNat + 4 + m ≤ 2 ^ 32)
    {rs : List Region} (hm : ⟨argAddr s 0, m⟩ ∈ rs) : InRegions rs (argAddr s j) 4 := by
  refine ⟨_, hm, ?_⟩
  rw [argAddr, argAddr, show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s.gpr .esp) 4
    from rfl, show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j)).setWidth 64 = addr (s.gpr .esp) (4 + 4 * j)
    from rfl, addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem addr_arg {e : BitVec 32} {B j : Nat} (s : State) (he : s.gpr .esp = e) :
    addr (e - BitVec.ofNat 32 B) (B + 4 + 4 * j) = argAddr s j := by
  rw [Nat.add_assoc, addr_above, ← he]; rfl

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem nosp_call {n : String} {c : Prog isa} (h : NoSp c) : NoSp (.call n c) := h

/-- The blocks storing arguments write only `eax` and memory. -/
theorem nosp_block {is : List Instr} (h : ∀ i ∈ is, Taint.clobbers i .esp = false) :
    NoSp (.block is) := h

theorem copy_nosp (B j k : Nat) : ∀ i ∈ copy B j k, Taint.clobbers i .esp = false := by
  intro i hi; simp only [copy, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem const_nosp (c k : Nat) : ∀ i ∈ const c k, Taint.clobbers i .esp = false := by
  intro i hi; simp only [const, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem buf_nosp (d k : Nat) : ∀ i ∈ buf d k, Taint.clobbers i .esp = false := by
  intro i hi; simp only [buf, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem append_nosp {a b : List Instr} (ha : ∀ i ∈ a, Taint.clobbers i .esp = false)
    (hb : ∀ i ∈ b, Taint.clobbers i .esp = false) : ∀ i ∈ a ++ b, Taint.clobbers i .esp = false :=
  fun i hi => (List.mem_append.mp hi).elim (ha i) (hb i)

theorem covers_self {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, by simp, by simp⟩

/-! ## `update` -/

/-- `update rate`'s contract on x86: that of `absorb` (`Proof.Sha3.absorbX86`)
with the rate `rate`, and the 40 bytes of stack the frame and the call use. -/
def updateX86 (rate : Nat) : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩
    s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 640 ≤ 2 ^ 32 ∧ 40 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    (arg s 1).toNat < rate
  post s s' :=
    (∀ msg, Repr s.mem ((arg s 0).setWidth 64) rate msg → (arg s 1).toNat = msg.length % rate →
      Repr s'.mem ((arg s 0).setWidth 64) rate
        (msg ++ bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)) ∧
    (s'.gpr .eax).toNat = ((arg s 1).toNat + (arg s 3).toNat) % rate
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem updateArgs_eq (rate : Nat) : updateArgs rate = copy 24 0 0 ++ (const rate 1 ++
    (copy 24 1 2 ++ (copy 24 2 3 ++ (copy 24 3 4 ++ (copy 24 4 5 ++ []))))) := by
  simp only [updateArgs, List.append_assoc, List.append_nil]

theorem updateArgs_nosp (rate : Nat) : NoSp (.block (updateArgs rate)) := by
  rw [updateArgs_eq]
  exact append_nosp (copy_nosp _ _ _) (append_nosp (const_nosp _ _) (append_nosp (copy_nosp _ _ _)
    (append_nosp (copy_nosp _ _ _) (append_nosp (copy_nosp _ _ _) (append_nosp (copy_nosp _ _ _)
    fun _ h => absurd h List.not_mem_nil)))))

/-- `e - 4` after a frame of `B` bytes below `e`. -/
theorem ret_eq (e : BitVec 32) (B : Nat) :
    e - BitVec.ofNat 32 B - 4 = e - BitVec.ofNat 32 (B + 4) := by
  rw [BitVec.ofNat_add, BitVec.sub_sub]; rfl

/-- `absorb`'s arguments, from `update`'s. -/
def updVs (rate : Nat) (s : State) : List (BitVec 32) :=
  [arg s 0, BitVec.ofNat 32 rate, arg s 1, arg s 2, arg s 3, arg s 4]

/-- What `absorb` may read and write: `data`; the state, the working space
and its arguments. -/
def updRd (s : State) : List Region := [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩]
def updWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 4).setWidth 64, 640⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 24⟩]

theorem update_args {rate : Nat} {s : State} (hs : (updateX86 rate).pre s) :
    WP isa (.block (updateArgs rate)) (allocFrame 24 s)
      (ArgInv 24 (allocFrame 24 s) (s.gpr .esp - BitVec.ofNat 32 24) (updVs rate s) 6) := by
  obtain ⟨-, p2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e40, efit, -⟩ := hs
  have hR : Room 24 (s.gpr .esp - BitVec.ofNat 32 24) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hfr : (⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 24⟩ : Region) ∈ (allocFrame 24 s).wr := by
    rw [allocFrame_wr]; exact List.mem_cons_self
  have hargs : (⟨argAddr s 0, 20⟩ : Region) ∈ (allocFrame 24 s).rd ++ (allocFrame 24 s).wr := by
    simp [p2]
  have cin : ∀ j, j < 5 → InRegions ((allocFrame 24 s).rd ++ (allocFrame 24 s).wr)
      (addr (s.gpr .esp - BitVec.ofNat 32 24) (24 + 4 + 4 * j)) 4 := fun j hj => by
    rw [addr_arg s rfl]; exact arg_in (by omega) (by omega) hargs
  have cval : ∀ j, (allocFrame 24 s).mem.readW (addr (s.gpr .esp - BitVec.ofNat 32 24) (24 + 4 + 4 * j)) 32 =
      arg s j := fun j => by rw [addr_arg s rfl]; rfl
  have cj : ∀ j, j < 5 → (s.gpr .esp - BitVec.ofNat 32 24).toNat + 24 + 4 + 4 * j + 4 ≤ 2 ^ 32 :=
    fun j hj => by rw [sub_toNat (by omega)]; omega
  rw [updateArgs_eq]
  exact copy_step (vs := updVs rate s) (ArgInv.start (allocFrame_esp _ _)) hfr hR (by decide) (cj 0 (by decide))
    (cin 0 (by decide)) (cval 0).symm
    fun u₁ h₁ => const_step h₁ hfr hR (by decide) rfl
    fun u₂ h₂ => copy_step h₂ hfr hR (by decide) (cj 1 (by decide)) (cin 1 (by decide)) (cval 1).symm
    fun u₃ h₃ => copy_step h₃ hfr hR (by decide) (cj 2 (by decide)) (cin 2 (by decide)) (cval 2).symm
    fun u₄ h₄ => copy_step h₄ hfr hR (by decide) (cj 3 (by decide)) (cin 3 (by decide)) (cval 3).symm
    fun u₅ h₅ => copy_step h₅ hfr hR (by decide) (cj 4 (by decide)) (cin 4 (by decide)) (cval 4).symm
    fun _ hI => WP.block_nil hI

/-- `absorb`'s arguments, as it sees them. -/
theorem update_entry {rate : Nat} {s t : State} (hs : (updateX86 rate).pre s)
    (hI : ArgInv 24 (allocFrame 24 s) (s.gpr .esp - BitVec.ofNat 32 24) (updVs rate s) 6 t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = BitVec.ofNat 32 rate ∧
      arg t.callEntry 2 = arg s 1 ∧ arg t.callEntry 3 = arg s 2 ∧ arg t.callEntry 4 = arg s 3 ∧
      arg t.callEntry 5 = arg s 4 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e40, efit, -⟩ := hs
  have hR : Room 24 (s.gpr .esp - BitVec.ofNat 32 24) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hE4 : 4 ≤ (s.gpr .esp - BitVec.ofNat 32 24).toNat := by rw [sub_toNat (by omega)]; omega
  exact ⟨entry_arg hI hE4 hR (by decide) (i := 0) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 1) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 2) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 3) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 4) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 5) (by decide)⟩

/-- `absorb`'s precondition, and its permissions, at the call. -/
theorem update_pre {rate : Nat} (hr : rate ∈ rates) {s t : State} (hs : (updateX86 rate).pre s)
    (hI : ArgInv 24 (allocFrame 24 s) (s.gpr .esp - BitVec.ofNat 32 24) (updVs rate s) 6 t) :
    Proof.Sha3.absorbX86.pre (t.callEntry.withRegions (updRd s) (updWr s)) ∧
      Covers (updRd s ++ updWr s) (t.rd ++ t.wr) ∧ Covers (updWr s) t.wr := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := update_entry hs hI
  obtain ⟨p1, p2, d1, d2, d3, -, -, -, -, -, -, d10, d11, d12, f1, f2, f3, e40, efit, hpos⟩ := hs
  have hrt := rate_lt hr
  have eA := entry_argAddr hI.esp
  have eSp := entry_esp hI.esp
  rw [ret_eq] at eSp
  have hfb : (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24 := frame_base (by omega)
  have hrb : (s.gpr .esp - BitVec.ofNat 32 (24 + 4)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28 := frame_base (by omega)
  have hsb : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28 - (12 : BitVec 64) =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40 := by
    rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add]
  have sA := in_stack (s.gpr .esp) (a := 24) (k := 24) (S := 40) (by decide) (by decide)
  have sR := in_stack (s.gpr .esp) (a := 28) (k := 4) (S := 40) (by decide) (by decide)
  have sS := in_stack (s.gpr .esp) (a := 40) (k := 12) (S := 40) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 (by omega)
  refine ⟨?_, covers_self fun r hr => ?_, covers_self fun r hr => ?_⟩
  · simp only [Proof.Sha3.absorbX86, updRd, updWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp,
      hrate, hfb, hrb, hsb]
    refine ⟨trivial, trivial, d1, d2, d3, d10.sub_left sA, d11.sub_left sA, d12.sub_left sA,
      d10.sub_left sR, d11.sub_left sR, d12.sub_left sR, d10.sub_left sS, d11.sub_left sS,
      d12.sub_left sS, f1, f2, f3, ?_, ?_, hr, hpos⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
  · rw [hI.rd, hI.wr, allocFrame_rd, allocFrame_wr, p1, p2]
    simp only [updRd, updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · rw [hI.wr, allocFrame_wr, p2]
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp

theorem update_correct {rate : Nat} (hr : rate ∈ rates) {s : State} (hs : (updateX86 rate).pre s) :
    WP isa (update rate) s fun s' => abiPreserved s s' ∧ (updateX86 rate).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, -, d7, -, d9, d10, d11, -, -, -, -, e40, -, -⟩ := hs'
  have hrt := rate_lt hr
  unfold update
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega)
    (nosp_seq (updateArgs_nosp rate) (nosp_call absorb_nosp)) ?_
  refine WP.seq (WP.mono (update_args hs) fun t hI => ?_)
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := update_entry hs hI
  obtain ⟨hpre, hc, hw⟩ := update_pre hr hs hI
  have hfb : (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24 := frame_base (by omega)
  have sA := in_stack (s.gpr .esp) (a := 24) (k := 24) (S := 40) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 (by omega)
  refine WP.call (k := Proof.Sha3.absorbX86) Stream.Absorb.absorb_verified.1 absorb_nosp
    (by rw [absorb_stack, hI.esp, sub_toNat (by omega)]; omega) hpre hc hw
    fun s' _ _ hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  -- After the call, and the frame's freeing.
  have stk := stack_below (e := s.gpr .esp) (S := 40) (by omega)
  have fall : Frame [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 4).setWidth 64, 640⟩,
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩] s.mem s'.mem := by
    have f₁ := hI.frame.sub (rs' := [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 4).setWidth 64, 640⟩,
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩]) fun r hr => by
      rw [List.mem_singleton.mp hr, hfb]
      exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩, by simp, sA⟩
    refine f₁.trans (hf.sub fun r hr => ?_)
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨(arg s 4).setWidth 64, 640⟩, by simp, fun _ h => h⟩
    · rw [hfb]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩, by simp, sA⟩
    · refine ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 40, 40⟩, by simp, ?_⟩
      rw [absorb_stack, hI.esp, stk]
      exact below_inner (by decide) (by omega)
  have ef := entry_frame (S := 40) hI rfl (by decide) (by omega)
  rw [allocFrame_mem] at ef
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hp => ?_, ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [freed_esp, hcs .esp (by simp [calleeSaved]), hI.esp]; exact BitVec.sub_add_cancel _ _
    · have hne : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
      rw [freed_gpr _ _ h, hcs r hr, hI.gpr r hne, allocFrame_gpr _ _ h]
  · rw [freed_mem]
    refine fall.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d7
    · exact d9
    · exact Offset.base_disjoint_below _ (by decide)
  · simp only [Proof.Sha3.absorbX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4,
      hrate] at hpost
    have hst : stateAt t.callEntry.mem ((arg s 0).setWidth 64) = stateAt s.mem ((arg s 0).setWidth 64) :=
      stateAt_frame ef fun r hr => by rw [List.mem_singleton.mp hr]; exact d10.symm
    have hd : bytesAt t.callEntry.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
        bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat :=
      bytesAt_frame ef (fun r hr => by rw [List.mem_singleton.mp hr]; exact d11.symm)
        (by have := (arg s 3).isLt; omega)
    have := hpost.1 msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) hp
    rw [hd, hm₂] at this
    rw [freed_mem]; exact this
  · simp only [Proof.Sha3.absorbX86, arg_withRegions, a0, a1, a2, a3, a4, hrate] at hpost
    rw [freed_gpr _ _ (by decide), ← hg₂ .eax (by decide)]
    exact hpost.2

/-- What holds after `update`'s block of arguments, from `σ`. -/
def updInv (rate : Nat) (σ t : State) : Prop :=
  ArgInv 24 (allocFrame 24 σ) (σ.gpr .esp - BitVec.ofNat 32 24) (updVs rate σ) 6 t

/-- `update`'s constant time, from the taint analysis of its block of
arguments. -/
theorem update_ct {rate : Nat} (hr : rate ∈ rates) {h : VG.Taint.Hint VG.X86.Taint.T}
    (hb : (taint.check (τr [.esp]) (.block (updateArgs rate)) h).isSome = true) :
    ConstantTime isa (updateX86 rate).pre (updateX86 rate).pub (update rate) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, ha⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (update rate) fun _ _ => True := by
    unfold update
    refine RelCT.frameAlloc (R := fun _ _ => True) (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := updInv rate σ₁) (F₂ := updInv rate σ₂)
      (RelCT.taint (A := taint) (τr [.esp]) (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr, ea, eb, e₁, e₂, allocFrame_esp, allocFrame_esp, hsp]) hb)
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨update_args p₁, update_args p₂⟩) ?_)
    refine RelCT.call Stream.Absorb.absorb_verified.1 Stream.Absorb.absorb_verified.2.1
      (updRd σ₁) (updWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_)
    obtain ⟨q1, q2, q3⟩ := update_pre hr p₁ ha'
    obtain ⟨r1, r2, r3⟩ := update_pre hr p₂ hb'
    have er : updRd σ₂ = updRd σ₁ := by simp only [updRd, ha 2 (by decide), ha 3 (by decide)]
    have ew : updWr σ₂ = updWr σ₁ := by simp only [updWr, ha 0 (by decide), ha 4 (by decide), hsp]
    rw [er, ew] at r1 r2
    rw [ew] at r3
    obtain ⟨x0, x1, x2, x3, x4, x5⟩ := update_entry p₁ ha'
    obtain ⟨y0, y1, y2, y3, y4, y5⟩ := update_entry p₂ hb'
    refine ⟨q1, r1, ⟨?_, fun i hi => ?_⟩, q2, q3, r2, r3, by rw [ha'.esp, hb'.esp, hsp]⟩
    · simp only [State.withRegions_gpr, State.callEntry_esp, ha'.esp, hb'.esp, hsp]
    · simp only [arg_withRegions]
      match i, hi with
      | 0, _ => rw [x0, y0, ha 0 (by decide)]
      | 1, _ => rw [x1, y1]
      | 2, _ => rw [x2, y2, ha 1 (by decide)]
      | 3, _ => rw [x3, y3, ha 2 (by decide)]
      | 4, _ => rw [x4, y4, ha 3 (by decide)]
      | 5, _ => rw [x5, y5, ha 4 (by decide)]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Memory holding `update`'s arguments `0x1000, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def updSatMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x400D then 0x20 else if a = 0x4015 then 0x30 else 0

/-- A state satisfying `updateX86`'s precondition (with no data). -/
def updSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := updSatMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩, ⟨0x4004, 20⟩]

theorem updSat_pre {rate : Nat} (hr : rate ∈ rates) : (updateX86 rate).pre updSat := by
  have a0 : arg updSat 0 = 0x1000 := by decide
  have a1 : arg updSat 1 = 0 := by decide
  have a2 : arg updSat 2 = 0x2000 := by decide
  have a3 : arg updSat 3 = 0 := by decide
  have a4 : arg updSat 4 = 0x3000 := by decide
  have e : argAddr updSat 0 = 0x4004 := by decide
  have h0 : 0 < rate := by simp [rates] at hr; omega
  simp only [updateX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, h0⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem update_verified {rate : Nat} (hr : rate ∈ rates)
    (hct : ConstantTime isa (updateX86 rate).pre (updateX86 rate).pub (update rate)) :
    Verified X86.target (update rate) (Spec.Sha3.updateContract X86.abi rate 40) :=
  (show Verified X86.target (update rate) (updateX86 rate) from
    ⟨fun s hs => (update_correct hr hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      ⟨updSat, updSat_pre hr⟩⟩).of_implies
    { pre := by implies_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
          Shared.setWidth_append32]
      post := by implies_post [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
          Shared.setWidth_append32]
      pub := by implies_pub [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, updateX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
          Shared.setWidth_append32]
      sat := ⟨updSat, by
        have h0 : 0 < rate := by simp [rates] at hr; omega
        sig_pre [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre,
          Spec.Sha3.updatePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, updSat, updSatMem,
          X86.arg, X86.argAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (simp; omega)⟩ }

theorem update_sha3_224 :
    Verified X86.target (update Spec.Sha3.hashSha3_224.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_224.rate 40) :=
  update_verified (by decide) (update_ct (by decide) (by taint_decide))

theorem update_sha3_256 :
    Verified X86.target (update Spec.Sha3.hashSha3_256.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_256.rate 40) :=
  update_verified (by decide) (update_ct (by decide) (by taint_decide))

theorem update_sha3_384 :
    Verified X86.target (update Spec.Sha3.hashSha3_384.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_384.rate 40) :=
  update_verified (by decide) (update_ct (by decide) (by taint_decide))

theorem update_sha3_512 :
    Verified X86.target (update Spec.Sha3.hashSha3_512.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.hashSha3_512.rate 40) :=
  update_verified (by decide) (update_ct (by decide) (by taint_decide))

theorem update_shake128 :
    Verified X86.target (update Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.xofShake128.rate 40) :=
  update_verified (by decide) (update_ct (by decide) (by taint_decide))

theorem update_shake256 :
    Verified X86.target (update Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.updateContract X86.abi Spec.Sha3.xofShake256.rate 40) :=
  update_verified (by decide) (update_ct (by decide) (by taint_decide))

/-- Two regions below `p`, apart. -/
theorem bdisj (p : Addr) (c : Nat) {a n b k : Nat} (ha : a ≤ c) (hb : b ≤ c)
    (h : c - a + n ≤ c - b ∨ c - b + k ≤ c - a) (hn : c - a + n ≤ 2 ^ 64) (hk : c - b + k ≤ 2 ^ 64) :
    Region.Disjoint ⟨p - BitVec.ofNat 64 a, n⟩ ⟨p - BitVec.ofNat 64 b, k⟩ := fun x h₁ h₂ =>
  Offset.sep_below p c ha hb h hn hk x
    (by simp only [Region.Contains] at h₁; omega) (by simp only [Region.Contains] at h₂; omega)

/-! ## SHAKE's `finalize` -/

/-- SHAKE's `finalize`'s contract on x86 for `X`: `pad`'s, with SHAKE's
suffix, its working space in the frame, and the 676 bytes of stack the
frame and the call use. -/
def xofFinX86 (X : Xof) : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩
    s.rd = [] ∧ s.wr = [state, args] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    stack.Disjoint state ∧ (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ 676 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 ∧ (arg s 1).toNat < X.rate
  post s s' := ∀ msg, Repr s.mem ((arg s 0).setWidth 64) X.rate msg →
    (arg s 1).toNat = msg.length % X.rate → XofRepr s'.mem ((arg s 0).setWidth 64) X.rate 0 X.xof msg 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i

theorem xofPadArgs_eq (rate : Nat) : xofPadArgs rate = copy 660 0 0 ++ (const rate 1 ++
    (copy 660 1 2 ++ (const 0x1f 3 ++ (buf 20 4 ++ [])))) := by
  simp only [xofPadArgs, List.append_assoc, List.append_nil]

theorem xofPadArgs_nosp (rate : Nat) : NoSp (.block (xofPadArgs rate)) := by
  rw [xofPadArgs_eq]
  exact append_nosp (copy_nosp _ _ _) (append_nosp (const_nosp _ _) (append_nosp (copy_nosp _ _ _)
    (append_nosp (const_nosp _ _) (append_nosp (buf_nosp _ _) fun _ h => absurd h List.not_mem_nil))))

/-- `pad`'s arguments, from SHAKE's `finalize`'s. -/
def xpVs (rate : Nat) (s : State) : List (BitVec 32) :=
  [arg s 0, BitVec.ofNat 32 rate, arg s 1, BitVec.ofNat 32 0x1f,
    s.gpr .esp - BitVec.ofNat 32 660 + BitVec.ofNat 32 20]

def xpWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 200⟩, ⟨(s.gpr .esp - BitVec.ofNat 32 660 + BitVec.ofNat 32 20).setWidth 64, 640⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 660).setWidth 64, 20⟩]

def xpInv (rate : Nat) (σ t : State) : Prop :=
  ArgInv 660 (allocFrame 660 σ) (σ.gpr .esp - BitVec.ofNat 32 660) (xpVs rate σ) 5 t

theorem xof_args {X : Xof} {s : State} (hs : (xofFinX86 X).pre s) :
    WP isa (.block (xofPadArgs X.rate)) (allocFrame 660 s) (xpInv X.rate s) := by
  obtain ⟨-, p2, -, -, -, -, e676, efit, -⟩ := hs
  have hR : Room 660 (s.gpr .esp - BitVec.ofNat 32 660) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hfr : (⟨(s.gpr .esp - BitVec.ofNat 32 660).setWidth 64, 660⟩ : Region) ∈ (allocFrame 660 s).wr := by
    rw [allocFrame_wr]; exact List.mem_cons_self
  have hargs : (⟨argAddr s 0, 8⟩ : Region) ∈ (allocFrame 660 s).rd ++ (allocFrame 660 s).wr := by
    simp [p2]
  have cin : ∀ j, j < 2 → InRegions ((allocFrame 660 s).rd ++ (allocFrame 660 s).wr)
      (addr (s.gpr .esp - BitVec.ofNat 32 660) (660 + 4 + 4 * j)) 4 := fun j hj => by
    rw [addr_arg s rfl]; exact arg_in (by omega) (by omega) hargs
  have cval : ∀ j, (allocFrame 660 s).mem.readW
      (addr (s.gpr .esp - BitVec.ofNat 32 660) (660 + 4 + 4 * j)) 32 = arg s j := fun j => by
    rw [addr_arg s rfl]; rfl
  have cj : ∀ j, j < 2 → (s.gpr .esp - BitVec.ofNat 32 660).toNat + 660 + 4 + 4 * j + 4 ≤ 2 ^ 32 :=
    fun j hj => by rw [sub_toNat (by omega)]; omega
  rw [xofPadArgs_eq]
  exact copy_step (vs := xpVs X.rate s) (ArgInv.start (allocFrame_esp _ _)) hfr hR (by decide)
    (cj 0 (by decide)) (cin 0 (by decide)) (cval 0).symm
    fun u₁ h₁ => const_step h₁ hfr hR (by decide) rfl
    fun u₂ h₂ => copy_step h₂ hfr hR (by decide) (cj 1 (by decide)) (cin 1 (by decide)) (cval 1).symm
    fun u₃ h₃ => const_step h₃ hfr hR (by decide) rfl
    fun u₄ h₄ => buf_step h₄ hfr hR (by decide) rfl
    fun _ hI => WP.block_nil hI

theorem xof_entry {rate : Nat} {s t : State} (e676 : 676 ≤ (s.gpr .esp).toNat)
    (efit : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32) (hI : xpInv rate s t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = BitVec.ofNat 32 rate ∧
      arg t.callEntry 2 = arg s 1 ∧ arg t.callEntry 3 = BitVec.ofNat 32 0x1f ∧
      arg t.callEntry 4 = s.gpr .esp - BitVec.ofNat 32 660 + BitVec.ofNat 32 20 := by
  have hR : Room 660 (s.gpr .esp - BitVec.ofNat 32 660) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hE4 : 4 ≤ (s.gpr .esp - BitVec.ofNat 32 660).toNat := by rw [sub_toNat (by omega)]; omega
  exact ⟨entry_arg hI hE4 hR (by decide) (i := 0) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 1) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 2) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 3) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 4) (by decide)⟩

/-- The working space at `e - 660 + 20`. -/
theorem scr_eq (e : BitVec 32) {B d : Nat} (hB : B ≤ e.toNat) (hd : d ≤ B) :
    (e - BitVec.ofNat 32 B + BitVec.ofNat 32 d).setWidth 64 = e.setWidth 64 - BitVec.ofNat 64 (B - d) :=
  addr_frame hB hd

theorem xof_pre {X : Xof} (hr : X.rate ∈ rates) {s t : State} (hs : (xofFinX86 X).pre s)
    (hI : xpInv X.rate s t) :
    Proof.Sha3.padX86.pre (t.callEntry.withRegions [] (xpWr s)) ∧
      Covers ([] ++ xpWr s) (t.rd ++ t.wr) ∧ Covers (xpWr s) t.wr := by
  obtain ⟨p1, p2, -, -, d3, f1, e676, efit, hpos⟩ := hs
  obtain ⟨a0, a1, a2, -, a4⟩ := xof_entry e676 efit hI
  have hrt := rate_lt hr
  have eA := entry_argAddr hI.esp
  have eSp := entry_esp hI.esp
  rw [ret_eq] at eSp
  have hfb : (s.gpr .esp - BitVec.ofNat 32 660).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 660 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 660 + BitVec.ofNat 32 20).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have hrb : (s.gpr .esp - BitVec.ofNat 32 (660 + 4)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsb : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 - (12 : BitVec 64) =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676 := by
    rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add]
  have sA := in_stack (s.gpr .esp) (a := 660) (k := 20) (S := 676) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 676) (by decide) (by decide)
  have sR := in_stack (s.gpr .esp) (a := 664) (k := 4) (S := 676) (by decide) (by decide)
  have sS := in_stack (s.gpr .esp) (a := 676) (k := 12) (S := 676) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by omega)
  have hP : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 660 + BitVec.ofNat 64 20 :=
    Offset.sub_ofNat_eq _ (by decide)
  have hQ : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676 + BitVec.ofNat 64 12 :=
    Offset.sub_ofNat_eq _ (by decide)
  have hpl : ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676).toNat = (s.gpr .esp).toNat - 676 := by
    rw [← frame_base (by omega), setWidth_toNat, sub_toNat (by omega)]
  have hw : ∀ r ∈ xpWr s, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := by
    intro r hr
    rw [hI.wr, allocFrame_wr, p2]
    simp only [xpWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, 0, by simp, by simp⟩
    · refine ⟨⟨(s.gpr .esp - BitVec.ofNat 32 660).setWidth 64, 660⟩, by simp, 20, ?_, by simp⟩
      exact addr_eq (x := s.gpr .esp - BitVec.ofNat 32 660) (k := 20) (by rw [sub_toNat (by omega)]; omega)
    · exact ⟨⟨(s.gpr .esp - BitVec.ofNat 32 660).setWidth 64, 660⟩, by simp, 0, by simp, by simp⟩
  refine ⟨?_, Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  · simp only [Proof.Sha3.padX86, xpWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a4, eA, eSp,
      hrate, hfb, hrb, hsb, hsc]
    refine ⟨trivial, trivial, (d3.sub_left sC).symm, d3.sub_left sA,
      bdisj _ 676 (by decide) (by decide) (by decide) (by decide) (by decide), d3.sub_left sR,
      bdisj _ 676 (by decide) (by decide) (by decide) (by decide) (by decide), d3.sub_left sS,
      bdisj _ 676 (by decide) (by decide) (by decide) (by decide) (by decide), f1, ?_, ?_, ?_, hr, hpos⟩
    · rw [BitVec.toNat_add, sub_toNat (by omega), BitVec.toNat_ofNat]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
  · obtain ⟨r', hr', o, ho⟩ := hw r (by simpa using hr)
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

theorem xof_correct {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates) {s : State}
    (hs : (xofFinX86 X).pre s) :
    WP isa (xofFinalize X.rate) s fun s' => abiPreserved s s' ∧ (xofFinX86 X).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, d2, d3, -, e676, efit, -⟩ := hs'
  have hrt := rate_lt hr
  unfold xofFinalize
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega)
    (nosp_seq (xofPadArgs_nosp _) (nosp_call pad_nosp)) ?_
  refine WP.seq (WP.mono (xof_args hs) fun t hI => ?_)
  obtain ⟨a0, a1, a2, a3, -⟩ := xof_entry e676 efit hI
  obtain ⟨hpre, hc, hw⟩ := xof_pre hr hs hI
  have hfb : (s.gpr .esp - BitVec.ofNat 32 660).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 660 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 660 + BitVec.ofNat 32 20).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have sA := in_stack (s.gpr .esp) (a := 660) (k := 20) (S := 676) (by decide) (by decide)
  have sF := in_stack (s.gpr .esp) (a := 660) (k := 660) (S := 676) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 676) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by omega)
  refine WP.call (k := Proof.Sha3.padX86) Stream.Pad.pad_verified.1 pad_nosp
    (by rw [pad_stack, hI.esp, sub_toNat (by omega)]; omega) hpre hc hw
    fun s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have stk := stack_below (e := s.gpr .esp) (S := 676) (by omega)
  have fall : Frame [⟨(arg s 0).setWidth 64, 200⟩,
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩] s.mem s'.mem := by
    have f₁ := hI.frame.sub (rs' := [⟨(arg s 0).setWidth 64, 200⟩,
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩]) fun r hr => by
      rw [List.mem_singleton.mp hr, hfb]
      exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩, by simp, sF⟩
    refine f₁.trans (hf.sub fun r hr => ?_)
    simp only [xpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, fun _ h => h⟩
    · rw [hsc]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩, by simp, sC⟩
    · rw [hfb]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩, by simp, sA⟩
    · refine ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 676, 676⟩, by simp, ?_⟩
      rw [pad_stack, hI.esp, stk]
      exact below_inner (by decide) (by omega)
  have ef := entry_frame (S := 676) hI rfl (by decide) (by omega)
  rw [allocFrame_mem] at ef
  have hsuf : (BitVec.ofNat 32 0x1f).setWidth 8 = Spec.Sha3.shakeSuffix := by decide
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hp => ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [freed_esp, hcs .esp (by simp [calleeSaved]), hI.esp]; exact BitVec.sub_add_cancel _ _
    · have hne : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
      rw [freed_gpr _ _ h, hcs r hr, hI.gpr r hne, allocFrame_gpr _ _ h]
  · rw [freed_mem]
    refine fall.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact d2
    · exact Offset.base_disjoint_below _ (by decide)
  · simp only [Proof.Sha3.padX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3,
      hrate, hsuf] at hpost
    have hst : stateAt t.callEntry.mem ((arg s 0).setWidth 64) = stateAt s.mem ((arg s 0).setWidth 64) :=
      stateAt_frame ef fun r hr => by rw [List.mem_singleton.mp hr]; exact d3.symm
    have := hpost msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) hp
    rw [hm₂] at this
    rw [freed_mem]; exact xofRepr_pad hX this

theorem xof_ct {X : Xof} (hr : X.rate ∈ rates) {h : VG.Taint.Hint VG.X86.Taint.T}
    (hb : (taint.check (τr [.esp]) (.block (xofPadArgs X.rate)) h).isSome = true) :
    ConstantTime isa (xofFinX86 X).pre (xofFinX86 X).pub (xofFinalize X.rate) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, ha⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (xofFinalize X.rate) fun _ _ => True := by
    unfold xofFinalize
    refine RelCT.frameAlloc (R := fun _ _ => True) (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := xpInv X.rate σ₁) (F₂ := xpInv X.rate σ₂)
      (RelCT.taint (A := taint) (τr [.esp]) (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr, ea, eb, e₁, e₂, allocFrame_esp, allocFrame_esp, hsp]) hb)
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨xof_args p₁, xof_args p₂⟩) ?_)
    refine RelCT.call Stream.Pad.pad_verified.1 Stream.Pad.pad_verified.2.1
      [] (xpWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_)
    obtain ⟨q1, q2, q3⟩ := xof_pre hr p₁ ha'
    obtain ⟨r1, r2, r3⟩ := xof_pre hr p₂ hb'
    have ew : xpWr σ₂ = xpWr σ₁ := by simp only [xpWr, ha 0 (by decide), hsp]
    rw [ew] at r1 r2 r3
    obtain ⟨x0, x1, x2, x3, x4⟩ := xof_entry p₁.2.2.2.2.2.2.1 p₁.2.2.2.2.2.2.2.1 ha'
    obtain ⟨y0, y1, y2, y3, y4⟩ := xof_entry p₂.2.2.2.2.2.2.1 p₂.2.2.2.2.2.2.2.1 hb'
    refine ⟨q1, r1, ⟨?_, fun i hi => ?_⟩, q2, q3, r2, r3, by rw [ha'.esp, hb'.esp, hsp]⟩
    · simp only [State.withRegions_gpr, State.callEntry_esp, ha'.esp, hb'.esp, hsp]
    · simp only [arg_withRegions]
      match i, hi with
      | 0, _ => rw [x0, y0, ha 0 (by decide)]
      | 1, _ => rw [x1, y1]
      | 2, _ => rw [x2, y2, ha 1 (by decide)]
      | 3, _ => rw [x3, y3]
      | 4, _ => rw [x4, y4, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Memory holding SHAKE's `finalize`'s arguments `0x1000, 0` at `0x4004`. -/
def xofSatMem : Mem := fun a => if a = 0x4005 then 0x10 else 0

def xofSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := xofSatMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x4004, 8⟩]

theorem xofSat_pre {X : Xof} (hr : X.rate ∈ rates) : (xofFinX86 X).pre xofSat := by
  have a0 : arg xofSat 0 = 0x1000 := by decide
  have a1 : arg xofSat 1 = 0 := by decide
  have e : argAddr xofSat 0 = 0x4004 := by decide
  have h0 : 0 < X.rate := by simp [rates] at hr; omega
  simp only [xofFinX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide, h0⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem xofFinalize_verified {X : Xof} (hX : xofSponge X) (hr : X.rate ∈ rates)
    (hct : ConstantTime isa (xofFinX86 X).pre (xofFinX86 X).pub (xofFinalize X.rate)) :
    Verified X86.target (xofFinalize X.rate) (Spec.Sha3.xofFinalizeContract X86.abi X 676) :=
  (show Verified X86.target (xofFinalize X.rate) (xofFinX86 X) from
    ⟨fun s hs => (xof_correct hX hr hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      ⟨xofSat, xofSat_pre hr⟩⟩).of_implies
    { pre := by implies_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofFinX86, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes]
      post := by implies_post [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofFinX86, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes]
      pub := by implies_pub [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig,
          Spec.Sha3.xofFinalizePre, Spec.Sha3.xofFinalizePost, xofFinX86, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes]
      sat := ⟨xofSat, by
        have h0 : 0 < X.rate := by simp [rates] at hr; omega
        sig_pre [Spec.Sha3.xofFinalizeContract, Spec.Sha3.xofFinalizeSig, Spec.Sha3.xofFinalizePre,
          Spec.Sha3.xofFinalizePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, xofSat,
          xofSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (simp; omega)⟩ }

theorem finalize_shake128 :
    Verified X86.target (xofFinalize Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofFinalizeContract X86.abi Spec.Sha3.xofShake128 676) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake128_sponge (by decide)
    (xof_ct (by decide) (by taint_decide))

theorem finalize_shake256 :
    Verified X86.target (xofFinalize Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofFinalizeContract X86.abi Spec.Sha3.xofShake256 676) :=
  xofFinalize_verified VG.Proof.Sha3.Instances.shake256_sponge (by decide)
    (xof_ct (by decide) (by taint_decide))

/-! ## SHAKE's `squeeze` -/

/-- SHAKE's `squeeze`'s contract on x86 for `X`: `squeeze`'s, its working
space in the frame, and the 680 bytes of stack the frame and the call use. -/
def xofSqzX86 (X : Xof) : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let out : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩
    s.rd = [] ∧ s.wr = [state, out, args] ∧ state.Disjoint out ∧
    args.Disjoint state ∧ args.Disjoint out ∧ ret.Disjoint state ∧ ret.Disjoint out ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    680 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ (arg s 1).toNat ≤ X.rate
  post s s' :=
    (∀ msg n, XofRepr s.mem ((arg s 0).setWidth 64) X.rate (arg s 1).toNat X.xof msg n →
      bytesAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
        (X.xof msg (n + (arg s 3).toNat)).drop n ∧
      XofRepr s'.mem ((arg s 0).setWidth 64) X.rate (s'.gpr .eax).toNat X.xof msg
        (n + (arg s 3).toNat)) ∧
    (s'.gpr .eax).toNat ≤ X.rate
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

theorem xofSqueezeArgs_eq (rate : Nat) : xofSqueezeArgs rate = copy 664 0 0 ++ (const rate 1 ++
    (copy 664 1 2 ++ (copy 664 2 3 ++ (copy 664 3 4 ++ (buf 24 5 ++ []))))) := by
  simp only [xofSqueezeArgs, List.append_assoc, List.append_nil]

theorem xofSqueezeArgs_nosp (rate : Nat) : NoSp (.block (xofSqueezeArgs rate)) := by
  rw [xofSqueezeArgs_eq]
  exact append_nosp (copy_nosp _ _ _) (append_nosp (const_nosp _ _) (append_nosp (copy_nosp _ _ _)
    (append_nosp (copy_nosp _ _ _) (append_nosp (copy_nosp _ _ _) (append_nosp (buf_nosp _ _)
    fun _ h => absurd h List.not_mem_nil)))))

/-- `squeeze`'s arguments, from SHAKE's `squeeze`'s. -/
def xsVs (rate : Nat) (s : State) : List (BitVec 32) :=
  [arg s 0, BitVec.ofNat 32 rate, arg s 1, arg s 2, arg s 3,
    s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24]

def xsWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64, 640⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 24⟩]

def xsInv (rate : Nat) (σ t : State) : Prop :=
  ArgInv 664 (allocFrame 664 σ) (σ.gpr .esp - BitVec.ofNat 32 664) (xsVs rate σ) 6 t

theorem xs_args {X : Xof} {s : State} (hs : (xofSqzX86 X).pre s) :
    WP isa (.block (xofSqueezeArgs X.rate)) (allocFrame 664 s) (xsInv X.rate s) := by
  obtain ⟨-, p2, -, -, -, -, -, -, -, -, -, e680, efit, -⟩ := hs
  have hR : Room 664 (s.gpr .esp - BitVec.ofNat 32 664) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hfr : (⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩ : Region) ∈ (allocFrame 664 s).wr := by
    rw [allocFrame_wr]; exact List.mem_cons_self
  have hargs : (⟨argAddr s 0, 16⟩ : Region) ∈ (allocFrame 664 s).rd ++ (allocFrame 664 s).wr := by
    simp [p2]
  have cin : ∀ j, j < 4 → InRegions ((allocFrame 664 s).rd ++ (allocFrame 664 s).wr)
      (addr (s.gpr .esp - BitVec.ofNat 32 664) (664 + 4 + 4 * j)) 4 := fun j hj => by
    rw [addr_arg s rfl]; exact arg_in (by omega) (by omega) hargs
  have cval : ∀ j, (allocFrame 664 s).mem.readW
      (addr (s.gpr .esp - BitVec.ofNat 32 664) (664 + 4 + 4 * j)) 32 = arg s j := fun j => by
    rw [addr_arg s rfl]; rfl
  have cj : ∀ j, j < 4 → (s.gpr .esp - BitVec.ofNat 32 664).toNat + 664 + 4 + 4 * j + 4 ≤ 2 ^ 32 :=
    fun j hj => by rw [sub_toNat (by omega)]; omega
  rw [xofSqueezeArgs_eq]
  exact copy_step (vs := xsVs X.rate s) (ArgInv.start (allocFrame_esp _ _)) hfr hR (by decide)
    (cj 0 (by decide)) (cin 0 (by decide)) (cval 0).symm
    fun u₁ h₁ => const_step h₁ hfr hR (by decide) rfl
    fun u₂ h₂ => copy_step h₂ hfr hR (by decide) (cj 1 (by decide)) (cin 1 (by decide)) (cval 1).symm
    fun u₃ h₃ => copy_step h₃ hfr hR (by decide) (cj 2 (by decide)) (cin 2 (by decide)) (cval 2).symm
    fun u₄ h₄ => copy_step h₄ hfr hR (by decide) (cj 3 (by decide)) (cin 3 (by decide)) (cval 3).symm
    fun u₅ h₅ => buf_step h₅ hfr hR (by decide) rfl
    fun _ hI => WP.block_nil hI

theorem xs_entry {rate : Nat} {s t : State} (e680 : 680 ≤ (s.gpr .esp).toNat)
    (efit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) (hI : xsInv rate s t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = BitVec.ofNat 32 rate ∧
      arg t.callEntry 2 = arg s 1 ∧ arg t.callEntry 3 = arg s 2 ∧ arg t.callEntry 4 = arg s 3 ∧
      arg t.callEntry 5 = s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24 := by
  have hR : Room 664 (s.gpr .esp - BitVec.ofNat 32 664) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hE4 : 4 ≤ (s.gpr .esp - BitVec.ofNat 32 664).toNat := by rw [sub_toNat (by omega)]; omega
  exact ⟨entry_arg hI hE4 hR (by decide) (i := 0) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 1) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 2) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 3) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 4) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 5) (by decide)⟩

theorem xs_pre {X : Xof} (hr : X.rate ∈ rates) {s t : State} (hs : (xofSqzX86 X).pre s)
    (hI : xsInv X.rate s t) :
    Proof.Sha3.squeezeX86.pre (t.callEntry.withRegions [] (xsWr s)) ∧
      Covers ([] ++ xsWr s) (t.rd ++ t.wr) ∧ Covers (xsWr s) t.wr := by
  obtain ⟨p1, p2, d1, -, -, -, -, d6, d7, f1, f2, e680, efit, hpos⟩ := hs
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := xs_entry e680 efit hI
  have hrt := rate_lt hr
  have eA := entry_argAddr hI.esp
  have eSp := entry_esp hI.esp
  rw [ret_eq] at eSp
  have hfb : (s.gpr .esp - BitVec.ofNat 32 664).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have hrb : (s.gpr .esp - BitVec.ofNat 32 (664 + 4)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 668 := frame_base (by omega)
  have hsb : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 668 - (12 : BitVec 64) =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680 := by
    rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add]
  have sA := in_stack (s.gpr .esp) (a := 664) (k := 24) (S := 680) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 680) (by decide) (by decide)
  have sR := in_stack (s.gpr .esp) (a := 668) (k := 4) (S := 680) (by decide) (by decide)
  have sS := in_stack (s.gpr .esp) (a := 680) (k := 12) (S := 680) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by omega)
  have hw : ∀ r ∈ xsWr s, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := by
    intro r hr
    rw [hI.wr, allocFrame_wr, p2]
    simp only [xsWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, by simp, 0, by simp, by simp⟩
    · refine ⟨⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩, by simp, 24, ?_, by simp⟩
      exact addr_eq (x := s.gpr .esp - BitVec.ofNat 32 664) (k := 24) (by rw [sub_toNat (by omega)]; omega)
    · exact ⟨⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩, by simp, 0, by simp, by simp⟩
  refine ⟨?_, Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  · simp only [Proof.Sha3.squeezeX86, xsWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp,
      hrate, hfb, hrb, hsb, hsc]
    refine ⟨trivial, trivial, d1, (d6.sub_left sC).symm, (d7.sub_left sC).symm, d6.sub_left sA,
      d7.sub_left sA, bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide),
      d6.sub_left sR, d7.sub_left sR,
      bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide), d6.sub_left sS,
      d7.sub_left sS, bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide),
      f1, f2, ?_, ?_, ?_, hr, hpos⟩
    · rw [BitVec.toNat_add, sub_toNat (by omega), BitVec.toNat_ofNat]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
  · obtain ⟨r', hr', o, ho⟩ := hw r (by simpa using hr)
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

theorem xs_correct {X : Xof} (hr : X.rate ∈ rates) {s : State} (hs : (xofSqzX86 X).pre s) :
    WP isa (xofSqueeze X.rate) s fun s' => abiPreserved s s' ∧ (xofSqzX86 X).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, -, -, d4, -, d6, d7, -, -, e680, efit, -⟩ := hs'
  have hrt := rate_lt hr
  unfold xofSqueeze
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega)
    (nosp_seq (xofSqueezeArgs_nosp _) (nosp_call squeeze_nosp)) ?_
  refine WP.seq (WP.mono (xs_args hs) fun t hI => ?_)
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := xs_entry e680 efit hI
  obtain ⟨hpre, hc, hw⟩ := xs_pre hr hs hI
  have hfb : (s.gpr .esp - BitVec.ofNat 32 664).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have sA := in_stack (s.gpr .esp) (a := 664) (k := 24) (S := 680) (by decide) (by decide)
  have sF := in_stack (s.gpr .esp) (a := 664) (k := 664) (S := 680) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 680) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 X.rate).toNat = X.rate := toNat_ofNat32 (by omega)
  refine WP.call (k := Proof.Sha3.squeezeX86) Stream.Squeeze.squeeze_verified.1 squeeze_nosp
    (by rw [squeeze_stack, hI.esp, sub_toNat (by omega)]; omega) hpre hc hw
    fun s' _ _ hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_
  have stk := stack_below (e := s.gpr .esp) (S := 680) (by omega)
  have fall : Frame [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩] s.mem s'.mem := by
    have f₁ := hI.frame.sub (rs' := [⟨(arg s 0).setWidth 64, 200⟩,
        ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩]) fun r hr => by
      rw [List.mem_singleton.mp hr, hfb]
      exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sF⟩
    refine f₁.trans (hf.sub fun r hr => ?_)
    simp only [xsWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, by simp, fun _ h => h⟩
    · rw [hsc]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sC⟩
    · rw [hfb]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sA⟩
    · refine ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, ?_⟩
      rw [squeeze_stack, hI.esp, stk]
      exact below_inner (by decide) (by omega)
  have ef := entry_frame (S := 680) hI rfl (by decide) (by omega)
  rw [allocFrame_mem] at ef
  have hst : stateAt t.callEntry.mem ((arg s 0).setWidth 64) = stateAt s.mem ((arg s 0).setWidth 64) :=
    stateAt_frame ef fun r hr => by rw [List.mem_singleton.mp hr]; exact d6.symm
  simp only [Proof.Sha3.squeezeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4,
    hrate, hst] at hpost
  obtain ⟨h1, h2, h3⟩ := hpost
  rw [hm₂] at h1 h3
  rw [hg₂ .eax (by decide)] at h2 h3
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg n hR => ?_, ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [freed_esp, hcs .esp (by simp [calleeSaved]), hI.esp]; exact BitVec.sub_add_cancel _ _
    · have hne : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
      rw [freed_gpr _ _ h, hcs r hr, hI.gpr r hne, allocFrame_gpr _ _ h]
  · rw [freed_mem]
    refine fall.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d4
    · exact hs.2.2.2.2.2.2.1
    · exact Offset.base_disjoint_below _ (by decide)
  · rw [freed_mem, freed_gpr _ _ (by decide)]
    exact xofRepr_squeeze hR h1 h3
  · rw [freed_gpr _ _ (by decide)]; exact h2

theorem xs_ct {X : Xof} (hr : X.rate ∈ rates) {h : VG.Taint.Hint VG.X86.Taint.T}
    (hb : (taint.check (τr [.esp]) (.block (xofSqueezeArgs X.rate)) h).isSome = true) :
    ConstantTime isa (xofSqzX86 X).pre (xofSqzX86 X).pub (xofSqueeze X.rate) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, ha⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (xofSqueeze X.rate) fun _ _ => True := by
    unfold xofSqueeze
    refine RelCT.frameAlloc (R := fun _ _ => True) (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := xsInv X.rate σ₁) (F₂ := xsInv X.rate σ₂)
      (RelCT.taint (A := taint) (τr [.esp]) (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr, ea, eb, e₁, e₂, allocFrame_esp, allocFrame_esp, hsp]) hb)
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨xs_args p₁, xs_args p₂⟩) ?_)
    refine RelCT.call Stream.Squeeze.squeeze_verified.1 Stream.Squeeze.squeeze_verified.2.1
      [] (xsWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_)
    obtain ⟨q1, q2, q3⟩ := xs_pre hr p₁ ha'
    obtain ⟨r1, r2, r3⟩ := xs_pre hr p₂ hb'
    have ew : xsWr σ₂ = xsWr σ₁ := by
      simp only [xsWr, ha 0 (by decide), ha 2 (by decide), ha 3 (by decide), hsp]
    rw [ew] at r1 r2 r3
    obtain ⟨x0, x1, x2, x3, x4, x5⟩ := xs_entry p₁.2.2.2.2.2.2.2.2.2.2.2.1 p₁.2.2.2.2.2.2.2.2.2.2.2.2.1 ha'
    obtain ⟨y0, y1, y2, y3, y4, y5⟩ := xs_entry p₂.2.2.2.2.2.2.2.2.2.2.2.1 p₂.2.2.2.2.2.2.2.2.2.2.2.2.1 hb'
    refine ⟨q1, r1, ⟨?_, fun i hi => ?_⟩, q2, q3, r2, r3, by rw [ha'.esp, hb'.esp, hsp]⟩
    · simp only [State.withRegions_gpr, State.callEntry_esp, ha'.esp, hb'.esp, hsp]
    · simp only [arg_withRegions]
      match i, hi with
      | 0, _ => rw [x0, y0, ha 0 (by decide)]
      | 1, _ => rw [x1, y1]
      | 2, _ => rw [x2, y2, ha 1 (by decide)]
      | 3, _ => rw [x3, y3, ha 2 (by decide)]
      | 4, _ => rw [x4, y4, ha 3 (by decide)]
      | 5, _ => rw [x5, y5, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Memory holding SHAKE's `squeeze`'s arguments `0x1000, 0, 0x2000, 0` at `0x4004`. -/
def xsSatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x400D then 0x20 else 0

def xsSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := xsSatMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x4004, 16⟩]

theorem xsSat_pre {X : Xof} : (xofSqzX86 X).pre xsSat := by
  have a0 : arg xsSat 0 = 0x1000 := by decide
  have a1 : arg xsSat 1 = 0 := by decide
  have a2 : arg xsSat 2 = 0x2000 := by decide
  have a3 : arg xsSat 3 = 0 := by decide
  have e : argAddr xsSat 0 = 0x4004 := by decide
  simp only [xofSqzX86, a0, a1, a2, a3, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    Nat.zero_le _⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem xofSqueeze_verified {X : Xof} (hr : X.rate ∈ rates)
    (hct : ConstantTime isa (xofSqzX86 X).pre (xofSqzX86 X).pub (xofSqueeze X.rate)) :
    Verified X86.target (xofSqueeze X.rate) (Spec.Sha3.xofSqueezeContract X86.abi X 680) :=
  (show Verified X86.target (xofSqueeze X.rate) (xofSqzX86 X) from
    ⟨fun s hs => (xs_correct hr hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      ⟨xsSat, xsSat_pre⟩⟩).of_implies
    { pre := by implies_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqzX86, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, Shared.setWidth_append32]
      post := by implies_post [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqzX86, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, Shared.setWidth_append32]
      pub := by implies_pub [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig,
          Spec.Sha3.xofSqueezePre, Spec.Sha3.xofSqueezePost, xofSqzX86, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, Shared.setWidth_append32]
      sat := ⟨xsSat, by
        sig_pre [Spec.Sha3.xofSqueezeContract, Spec.Sha3.xofSqueezeSig, Spec.Sha3.xofSqueezePre,
          Spec.Sha3.xofSqueezePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, xsSat,
          xsSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | simp⟩ }

theorem squeeze_shake128 :
    Verified X86.target (xofSqueeze Spec.Sha3.xofShake128.rate)
      (Spec.Sha3.xofSqueezeContract X86.abi Spec.Sha3.xofShake128 680) :=
  xofSqueeze_verified (by decide) (xs_ct (by decide) (by taint_decide))

theorem squeeze_shake256 :
    Verified X86.target (xofSqueeze Spec.Sha3.xofShake256.rate)
      (Spec.Sha3.xofSqueezeContract X86.abi Spec.Sha3.xofShake256 680) :=
  xofSqueeze_verified (by decide) (xs_ct (by decide) (by taint_decide))

/-! ## SHA-3's `finalize` -/

/-- SHA-3's `finalize`'s contract on x86 for `H`: `pad` with SHA-3's suffix
and then `squeeze` of the digest, their working space in the frame, and the
680 bytes of stack the frame and the calls use. -/
def finX86 (H : Spec.Sha3.HashFn) : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let out : Region := ⟨(arg s 2).setWidth 64, H.len⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩
    s.rd = [] ∧ s.wr = [state, out, args] ∧ state.Disjoint out ∧
    args.Disjoint state ∧ args.Disjoint out ∧ ret.Disjoint state ∧ ret.Disjoint out ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 2).toNat + H.len ≤ 2 ^ 32 ∧
    680 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat < H.rate
  post s s' := ∀ msg, Repr s.mem ((arg s 0).setWidth 64) H.rate msg →
    (arg s 1).toNat = msg.length % H.rate → bytesAt s'.mem ((arg s 2).setWidth 64) H.len = H.digest msg
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

theorem finPadArgs_eq (rate : Nat) : finPadArgs rate = copy 664 0 0 ++ (const rate 1 ++
    (copy 664 1 2 ++ (const 0x06 3 ++ (buf 24 4 ++ [])))) := by
  simp only [finPadArgs, List.append_assoc, List.append_nil]

theorem finSqzArgs_eq (rate len : Nat) : finSqzArgs rate len = copy 664 0 0 ++ (const rate 1 ++
    (const 0 2 ++ (copy 664 2 3 ++ (const len 4 ++ (buf 24 5 ++ []))))) := by
  simp only [finSqzArgs, List.append_assoc, List.append_nil]

theorem finalize_nosp (rate len : Nat) :
    NoSp (.seq (.block (finPadArgs rate)) <| .seq (.call "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) <|
      .seq (.block (finSqzArgs rate len)) (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) :
      Prog isa) := by
  refine nosp_seq ?_ (nosp_seq (nosp_call pad_nosp) (nosp_seq ?_ (nosp_call squeeze_nosp)))
  · rw [finPadArgs_eq]
    exact append_nosp (copy_nosp _ _ _) (append_nosp (const_nosp _ _) (append_nosp (copy_nosp _ _ _)
      (append_nosp (const_nosp _ _) (append_nosp (buf_nosp _ _) fun _ h => absurd h List.not_mem_nil))))
  · rw [finSqzArgs_eq]
    exact append_nosp (copy_nosp _ _ _) (append_nosp (const_nosp _ _) (append_nosp (const_nosp _ _)
      (append_nosp (copy_nosp _ _ _) (append_nosp (const_nosp _ _) (append_nosp (buf_nosp _ _)
      fun _ h => absurd h List.not_mem_nil)))))

/-- `pad`'s arguments, from SHA-3's `finalize`'s. -/
def fpVs (rate : Nat) (s : State) : List (BitVec 32) :=
  [arg s 0, BitVec.ofNat 32 rate, arg s 1, BitVec.ofNat 32 0x06,
    s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24]

def fpWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 200⟩, ⟨(s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64, 640⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 20⟩]

def fpInv (rate : Nat) (σ t : State) : Prop :=
  ArgInv 664 (allocFrame 664 σ) (σ.gpr .esp - BitVec.ofNat 32 664) (fpVs rate σ) 5 t

/-- `squeeze`'s arguments: the digest, from position 0. -/
def fsVs (rate len : Nat) (s : State) : List (BitVec 32) :=
  [arg s 0, BitVec.ofNat 32 rate, BitVec.ofNat 32 0, arg s 2, BitVec.ofNat 32 len,
    s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24]

def fsWr (len : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 2).setWidth 64, len⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64, 640⟩,
    ⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 24⟩]

/-- After the call of `pad`, from `s`. -/
structure AfterPad (H : Spec.Sha3.HashFn) (s u : State) : Prop where
  esp : u.gpr .esp = s.gpr .esp - BitVec.ofNat 32 664
  gpr : ∀ r ∈ calleeSaved, r ≠ .esp → u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = (allocFrame 664 s).wr
  frame : Frame [⟨(arg s 0).setWidth 64, 200⟩, ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩]
    s.mem u.mem
  args : ∀ j < 3, u.mem.readW (argAddr s j) 32 = arg s j
  pad : ∀ msg, Repr s.mem ((arg s 0).setWidth 64) H.rate msg → (arg s 1).toNat = msg.length % H.rate →
    stateAt u.mem ((arg s 0).setWidth 64) =
      Spec.Sha3.absorb H.rate (Spec.Sha3.pad H.rate Spec.Sha3.sha3Suffix msg)

def fsInv (H : Spec.Sha3.HashFn) (s t : State) : Prop :=
  ∃ u, AfterPad H s u ∧
    ArgInv 664 u (s.gpr .esp - BitVec.ofNat 32 664) (fsVs H.rate H.len s) 6 t

theorem fp_args {H : Spec.Sha3.HashFn} {s : State} (hs : (finX86 H).pre s) :
    WP isa (.block (finPadArgs H.rate)) (allocFrame 664 s) (fpInv H.rate s) := by
  obtain ⟨-, p2, -, -, -, -, -, -, -, -, -, e680, efit, -⟩ := hs
  have hR : Room 664 (s.gpr .esp - BitVec.ofNat 32 664) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hfr : (⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩ : Region) ∈ (allocFrame 664 s).wr := by
    rw [allocFrame_wr]; exact List.mem_cons_self
  have hargs : (⟨argAddr s 0, 12⟩ : Region) ∈ (allocFrame 664 s).rd ++ (allocFrame 664 s).wr := by
    simp [p2]
  have cin : ∀ j, j < 3 → InRegions ((allocFrame 664 s).rd ++ (allocFrame 664 s).wr)
      (addr (s.gpr .esp - BitVec.ofNat 32 664) (664 + 4 + 4 * j)) 4 := fun j hj => by
    rw [addr_arg s rfl]; exact arg_in (by omega) (by omega) hargs
  have cval : ∀ j, (allocFrame 664 s).mem.readW
      (addr (s.gpr .esp - BitVec.ofNat 32 664) (664 + 4 + 4 * j)) 32 = arg s j := fun j => by
    rw [addr_arg s rfl]; rfl
  have cj : ∀ j, j < 3 → (s.gpr .esp - BitVec.ofNat 32 664).toNat + 664 + 4 + 4 * j + 4 ≤ 2 ^ 32 :=
    fun j hj => by rw [sub_toNat (by omega)]; omega
  rw [finPadArgs_eq]
  exact copy_step (vs := fpVs H.rate s) (ArgInv.start (allocFrame_esp _ _)) hfr hR (by decide)
    (cj 0 (by decide)) (cin 0 (by decide)) (cval 0).symm
    fun u₁ h₁ => const_step h₁ hfr hR (by decide) rfl
    fun u₂ h₂ => copy_step h₂ hfr hR (by decide) (cj 1 (by decide)) (cin 1 (by decide)) (cval 1).symm
    fun u₃ h₃ => const_step h₃ hfr hR (by decide) rfl
    fun u₄ h₄ => buf_step h₄ hfr hR (by decide) rfl
    fun _ hI => WP.block_nil hI

theorem fp_entry {rate : Nat} {s t : State} (e680 : 680 ≤ (s.gpr .esp).toNat)
    (efit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32) (hI : fpInv rate s t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = BitVec.ofNat 32 rate ∧
      arg t.callEntry 2 = arg s 1 ∧ arg t.callEntry 3 = BitVec.ofNat 32 0x06 ∧
      arg t.callEntry 4 = s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24 := by
  have hR : Room 664 (s.gpr .esp - BitVec.ofNat 32 664) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hE4 : 4 ≤ (s.gpr .esp - BitVec.ofNat 32 664).toNat := by rw [sub_toNat (by omega)]; omega
  exact ⟨entry_arg hI hE4 hR (by decide) (i := 0) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 1) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 2) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 3) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 4) (by decide)⟩

theorem fp_pre {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {s t : State} (hs : (finX86 H).pre s)
    (hI : fpInv H.rate s t) :
    Proof.Sha3.padX86.pre (t.callEntry.withRegions [] (fpWr s)) ∧
      Covers ([] ++ fpWr s) (t.rd ++ t.wr) ∧ Covers (fpWr s) t.wr := by
  obtain ⟨p1, p2, -, -, -, -, -, d6, -, f1, -, e680, efit, hpos⟩ := hs
  obtain ⟨a0, a1, a2, -, a4⟩ := fp_entry e680 efit hI
  have hrt := rate_lt hr
  have eA := entry_argAddr hI.esp
  have eSp := entry_esp hI.esp
  rw [ret_eq] at eSp
  have hfb : (s.gpr .esp - BitVec.ofNat 32 664).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have hrb : (s.gpr .esp - BitVec.ofNat 32 (664 + 4)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 668 := frame_base (by omega)
  have hsb : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 668 - (12 : BitVec 64) =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680 := by
    rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add]
  have sA := in_stack (s.gpr .esp) (a := 664) (k := 20) (S := 680) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 680) (by decide) (by decide)
  have sR := in_stack (s.gpr .esp) (a := 668) (k := 4) (S := 680) (by decide) (by decide)
  have sS := in_stack (s.gpr .esp) (a := 680) (k := 12) (S := 680) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by omega)
  have hw : ∀ r ∈ fpWr s, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := by
    intro r hr
    rw [hI.wr, allocFrame_wr, p2]
    simp only [fpWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, 0, by simp, by simp⟩
    · refine ⟨⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩, by simp, 24, ?_, by simp⟩
      exact addr_eq (x := s.gpr .esp - BitVec.ofNat 32 664) (k := 24) (by rw [sub_toNat (by omega)]; omega)
    · exact ⟨⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩, by simp, 0, by simp, by simp⟩
  refine ⟨?_, Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  · simp only [Proof.Sha3.padX86, fpWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a4, eA, eSp,
      hrate, hfb, hrb, hsb, hsc]
    refine ⟨trivial, trivial, (d6.sub_left sC).symm, d6.sub_left sA,
      bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide), d6.sub_left sR,
      bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide), d6.sub_left sS,
      bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide), f1, ?_, ?_, ?_, hr, hpos⟩
    · rw [BitVec.toNat_add, sub_toNat (by omega), BitVec.toNat_ofNat]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
  · obtain ⟨r', hr', o, ho⟩ := hw r (by simpa using hr)
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

/-- The caller's argument `j` is outside the state and the stack below `esp`. -/
theorem arg_apart {s : State} {j n S : Nat} (hj : 4 * j + 4 ≤ n)
    (hS : S ≤ (s.gpr .esp).toNat) (hfit : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32)
    {R : Region} (hd : Region.Disjoint ⟨argAddr s 0, n⟩ R) :
    ∀ r ∈ [R, (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S, S⟩ : Region)],
      Region.Disjoint ⟨argAddr s j, 4⟩ r := by
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  have ej : argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) := addr_eq (by omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine hd.sub_left ?_
    rw [e0, ej]; exact Offset.sub _ (by omega) (by omega)
  · rw [ej]; exact Offset.disjoint_below _ (by have := (s.gpr .esp).isLt; omega)

theorem fp_call {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) {s t : State} (hs : (finX86 H).pre s)
    (hI : fpInv H.rate s t) :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) t (AfterPad H s) := by
  have hs' := hs
  obtain ⟨-, -, -, d4, -, -, -, d6, -, -, -, e680, efit, -⟩ := hs'
  have hrt := rate_lt hr
  obtain ⟨a0, a1, a2, a3, -⟩ := fp_entry e680 efit hI
  obtain ⟨hpre, hc, hw⟩ := fp_pre hr hs hI
  have hfb : (s.gpr .esp - BitVec.ofNat 32 664).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have sA := in_stack (s.gpr .esp) (a := 664) (k := 20) (S := 680) (by decide) (by decide)
  have sF := in_stack (s.gpr .esp) (a := 664) (k := 664) (S := 680) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 680) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by omega)
  refine WP.call (k := Proof.Sha3.padX86) Stream.Pad.pad_verified.1 pad_nosp
    (by rw [pad_stack, hI.esp, sub_toNat (by omega)]; omega) hpre hc hw
    fun s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have stk := stack_below (e := s.gpr .esp) (S := 680) (by omega)
  have fall : Frame [⟨(arg s 0).setWidth 64, 200⟩,
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩] s.mem s'.mem := by
    have f₁ := hI.frame.sub (rs' := [⟨(arg s 0).setWidth 64, 200⟩,
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩]) fun r hr => by
      rw [List.mem_singleton.mp hr, hfb]
      exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sF⟩
    refine f₁.trans (hf.sub fun r hr => ?_)
    simp only [fpWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, fun _ h => h⟩
    · rw [hsc]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sC⟩
    · rw [hfb]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sA⟩
    · refine ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, ?_⟩
      rw [pad_stack, hI.esp, stk]
      exact below_inner (by decide) (by omega)
  have ef := entry_frame (S := 680) hI rfl (by decide) (by omega)
  rw [allocFrame_mem] at ef
  have hsuf : (BitVec.ofNat 32 0x06).setWidth 8 = Spec.Sha3.sha3Suffix := by decide
  refine ⟨by rw [hcs .esp (by simp [calleeSaved]), hI.esp], fun r hr h => ?_, by rw [hrd, hI.rd]; rfl,
    by rw [hwr, hI.wr], fall, fun j hj => ?_, fun msg hm hp => ?_⟩
  · have hne : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
    rw [hcs r hr, hI.gpr r hne, allocFrame_gpr _ _ h]
  · exact fall.readW (r := ⟨argAddr s j, 4⟩) (Region.contains_self _ _)
      (arg_apart (by omega) (by omega) (by omega) d4) (by decide)
  · simp only [Proof.Sha3.padX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3,
      hrate, hsuf] at hpost
    have hst : stateAt t.callEntry.mem ((arg s 0).setWidth 64) = stateAt s.mem ((arg s 0).setWidth 64) :=
      stateAt_frame ef fun r hr => by rw [List.mem_singleton.mp hr]; exact d6.symm
    have := hpost msg (by unfold Spec.Sha3.Repr; rw [hst]; exact hm) hp
    rw [hm₂] at this; exact this

theorem fs_args {H : Spec.Sha3.HashFn} {s u : State} (hs : (finX86 H).pre s)
    (hA : AfterPad H s u) :
    WP isa (.block (finSqzArgs H.rate H.len)) u
      (ArgInv 664 u (s.gpr .esp - BitVec.ofNat 32 664) (fsVs H.rate H.len s) 6) := by
  obtain ⟨-, p2, -, -, -, -, -, -, -, -, -, e680, efit, -⟩ := hs
  have hR : Room 664 (s.gpr .esp - BitVec.ofNat 32 664) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hfr : (⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩ : Region) ∈ u.wr := by
    rw [hA.wr, allocFrame_wr]; exact List.mem_cons_self
  have hargs : (⟨argAddr s 0, 12⟩ : Region) ∈ u.rd ++ u.wr := by
    rw [hA.wr, allocFrame_wr, p2]; simp
  have cin : ∀ j, j < 3 → InRegions (u.rd ++ u.wr)
      (addr (s.gpr .esp - BitVec.ofNat 32 664) (664 + 4 + 4 * j)) 4 := fun j hj => by
    rw [addr_arg s rfl]; exact arg_in (by omega) (by omega) hargs
  have cval : ∀ j, j < 3 → u.mem.readW
      (addr (s.gpr .esp - BitVec.ofNat 32 664) (664 + 4 + 4 * j)) 32 = arg s j := fun j hj => by
    rw [addr_arg s rfl]; exact hA.args j hj
  have cj : ∀ j, j < 3 → (s.gpr .esp - BitVec.ofNat 32 664).toNat + 664 + 4 + 4 * j + 4 ≤ 2 ^ 32 :=
    fun j hj => by rw [sub_toNat (by omega)]; omega
  rw [finSqzArgs_eq]
  exact copy_step (vs := fsVs H.rate H.len s) (ArgInv.start hA.esp) hfr hR (by decide)
    (cj 0 (by decide)) (cin 0 (by decide)) (cval 0 (by decide)).symm
    fun u₁ h₁ => const_step h₁ hfr hR (by decide) rfl
    fun u₂ h₂ => const_step h₂ hfr hR (by decide) rfl
    fun u₃ h₃ => copy_step h₃ hfr hR (by decide) (cj 2 (by decide)) (cin 2 (by decide))
      (cval 2 (by decide)).symm
    fun u₄ h₄ => const_step h₄ hfr hR (by decide) rfl
    fun u₅ h₅ => buf_step h₅ hfr hR (by decide) rfl
    fun _ hI => WP.block_nil hI

theorem fs_entry {H : Spec.Sha3.HashFn} {s u t : State} (e680 : 680 ≤ (s.gpr .esp).toNat)
    (efit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32)
    (hI : ArgInv 664 u (s.gpr .esp - BitVec.ofNat 32 664) (fsVs H.rate H.len s) 6 t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = BitVec.ofNat 32 H.rate ∧
      arg t.callEntry 2 = BitVec.ofNat 32 0 ∧ arg t.callEntry 3 = arg s 2 ∧
      arg t.callEntry 4 = BitVec.ofNat 32 H.len ∧
      arg t.callEntry 5 = s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24 := by
  have hR : Room 664 (s.gpr .esp - BitVec.ofNat 32 664) := ⟨by rw [sub_toNat (by omega)]; omega⟩
  have hE4 : 4 ≤ (s.gpr .esp - BitVec.ofNat 32 664).toNat := by rw [sub_toNat (by omega)]; omega
  exact ⟨entry_arg hI hE4 hR (by decide) (i := 0) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 1) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 2) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 3) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 4) (by decide),
    entry_arg hI hE4 hR (by decide) (i := 5) (by decide)⟩

theorem fs_pre {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15) {s u t : State}
    (hs : (finX86 H).pre s) (hA : AfterPad H s u)
    (hI : ArgInv 664 u (s.gpr .esp - BitVec.ofNat 32 664) (fsVs H.rate H.len s) 6 t) :
    Proof.Sha3.squeezeX86.pre (t.callEntry.withRegions [] (fsWr H.len s)) ∧
      Covers ([] ++ fsWr H.len s) (t.rd ++ t.wr) ∧ Covers (fsWr H.len s) t.wr := by
  obtain ⟨p1, p2, d1, -, -, -, -, d6, d7, f1, f2, e680, efit, -⟩ := hs
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := fs_entry e680 efit hI
  have hrt := rate_lt hr
  have eA := entry_argAddr hI.esp
  have eSp := entry_esp hI.esp
  rw [ret_eq] at eSp
  have hfb : (s.gpr .esp - BitVec.ofNat 32 664).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have hrb : (s.gpr .esp - BitVec.ofNat 32 (664 + 4)).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 668 := frame_base (by omega)
  have hsb : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 668 - (12 : BitVec 64) =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680 := by
    rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add]
  have sA := in_stack (s.gpr .esp) (a := 664) (k := 24) (S := 680) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 680) (by decide) (by decide)
  have sR := in_stack (s.gpr .esp) (a := 668) (k := 4) (S := 680) (by decide) (by decide)
  have sS := in_stack (s.gpr .esp) (a := 680) (k := 12) (S := 680) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by omega)
  have hlen : (BitVec.ofNat 32 H.len).toNat = H.len := toNat_ofNat32 (by omega)
  have hw : ∀ r ∈ fsWr H.len s, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := by
    intro r hr
    rw [hI.wr, hA.wr, allocFrame_wr, p2]
    simp only [fsWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨(arg s 2).setWidth 64, H.len⟩, by simp, 0, by simp, by simp⟩
    · refine ⟨⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩, by simp, 24, ?_, by simp⟩
      exact addr_eq (x := s.gpr .esp - BitVec.ofNat 32 664) (k := 24) (by rw [sub_toNat (by omega)]; omega)
    · exact ⟨⟨(s.gpr .esp - BitVec.ofNat 32 664).setWidth 64, 664⟩, by simp, 0, by simp, by simp⟩
  refine ⟨?_, Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  · simp only [Proof.Sha3.squeezeX86, fsWr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp,
      hrate, hlen, hfb, hrb, hsb, hsc]
    refine ⟨trivial, trivial, d1, (d6.sub_left sC).symm, (d7.sub_left sC).symm, d6.sub_left sA,
      d7.sub_left sA, bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide),
      d6.sub_left sR, d7.sub_left sR,
      bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide), d6.sub_left sS,
      d7.sub_left sS, bdisj _ 680 (by decide) (by decide) (by decide) (by decide) (by decide),
      f1, f2, ?_, ?_, ?_, hr, by simp⟩
    · rw [BitVec.toNat_add, sub_toNat (by omega), BitVec.toNat_ofNat]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
  · obtain ⟨r', hr', o, ho⟩ := hw r (by simpa using hr)
    exact ⟨r', List.mem_append_right _ hr', o, ho⟩

theorem fin_correct {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15) {s : State} (hs : (finX86 H).pre s) :
    WP isa (finalize H.rate H.len) s fun s' => abiPreserved s s' ∧ (finX86 H).post s s' := by
  have hs' := hs
  obtain ⟨-, -, -, -, -, d4, d5, d6, d7, -, -, e680, efit, -⟩ := hs'
  have hrt := rate_lt hr
  unfold finalize
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (finalize_nosp _ _) ?_
  refine WP.seq (WP.mono (fp_args hs) fun t hI => ?_)
  refine WP.seq (WP.mono (fp_call hr hs hI) fun u hA => ?_)
  refine WP.seq (WP.mono (fs_args hs hA) fun t₂ hI₂ => ?_)
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := fs_entry e680 efit hI₂
  obtain ⟨hpre, hc, hw⟩ := fs_pre hr hl hs hA hI₂
  have hfb : (s.gpr .esp - BitVec.ofNat 32 664).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 664 := frame_base (by omega)
  have hsc : (s.gpr .esp - BitVec.ofNat 32 664 + BitVec.ofNat 32 24).setWidth 64 =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 640 := scr_eq (s.gpr .esp) (by omega) (by decide)
  have sA := in_stack (s.gpr .esp) (a := 664) (k := 24) (S := 680) (by decide) (by decide)
  have sF := in_stack (s.gpr .esp) (a := 664) (k := 664) (S := 680) (by decide) (by decide)
  have sC := in_stack (s.gpr .esp) (a := 640) (k := 640) (S := 680) (by decide) (by decide)
  have hrate : (BitVec.ofNat 32 H.rate).toNat = H.rate := toNat_ofNat32 (by omega)
  have hlen : (BitVec.ofNat 32 H.len).toNat = H.len := toNat_ofNat32 (by omega)
  refine WP.call (k := Proof.Sha3.squeezeX86) Stream.Squeeze.squeeze_verified.1 squeeze_nosp
    (by rw [squeeze_stack, hI₂.esp, sub_toNat (by omega)]; omega) hpre hc hw
    fun s' _ _ hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have stk := stack_below (e := s.gpr .esp) (S := 680) (by omega)
  have fall : Frame [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 2).setWidth 64, H.len⟩,
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩] s.mem s'.mem := by
    have f₀ := hA.frame.mono (rs' := [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 2).setWidth 64, H.len⟩,
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
    have f₁ := hI₂.frame.sub (rs' := [⟨(arg s 0).setWidth 64, 200⟩, ⟨(arg s 2).setWidth 64, H.len⟩,
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩]) fun r hr => by
      rw [List.mem_singleton.mp hr, hfb]
      exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sF⟩
    refine f₀.trans (f₁.trans (hf.sub fun r hr => ?_))
    simp only [fsWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨(arg s 0).setWidth 64, 200⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨(arg s 2).setWidth 64, H.len⟩, by simp, fun _ h => h⟩
    · rw [hsc]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sC⟩
    · rw [hfb]; exact ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, sA⟩
    · refine ⟨⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 680, 680⟩, by simp, ?_⟩
      rw [squeeze_stack, hI₂.esp, stk]
      exact below_inner (by decide) (by omega)
  have ef := entry_frame (S := 680) hI₂ rfl (by decide) (by omega)
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hp => ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [freed_esp, hcs .esp (by simp [calleeSaved]), hI₂.esp]; exact BitVec.sub_add_cancel _ _
    · have hne : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
      rw [freed_gpr _ _ h, hcs r hr, hI₂.gpr r hne, hA.gpr r hr h]
  · rw [freed_mem]
    refine fall.readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d4
    · exact d5
    · exact Offset.base_disjoint_below _ (by decide)
  · simp only [Proof.Sha3.squeezeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4,
      hrate, hlen] at hpost
    have hst : stateAt t₂.callEntry.mem ((arg s 0).setWidth 64) = stateAt u.mem ((arg s 0).setWidth 64) :=
      stateAt_frame ef fun r hr => by rw [List.mem_singleton.mp hr]; exact d6.symm
    rw [freed_mem, ← hm₂, hpost.1, hst, hA.pad msg hm hp]
    exact digest_of_pad hH rfl

theorem fin_ct {H : Spec.Sha3.HashFn} (hr : H.rate ∈ rates) (hl : H.len < 2 ^ 15)
    {h₁ h₂ : VG.Taint.Hint VG.X86.Taint.T}
    (hb₁ : (taint.check (τr [.esp]) (.block (finPadArgs H.rate)) h₁).isSome = true)
    (hb₂ : (taint.check (τr [.esp]) (.block (finSqzArgs H.rate H.len)) h₂).isSome = true) :
    ConstantTime isa (finX86 H).pre (finX86 H).pub (finalize H.rate H.len) := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' p₁ p₂ hp e₁ e₂
  obtain ⟨hsp, ha⟩ := hp
  have hP : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) (finalize H.rate H.len) fun _ _ => True := by
    unfold finalize
    refine RelCT.frameAlloc (R := fun _ _ => True) (RelCT.seq (Q := fun _ _ => True)
      (RelCT.wp (F₁ := fpInv H.rate σ₁) (F₂ := fpInv H.rate σ₂)
      (RelCT.taint (A := taint) (τr [.esp]) (fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr, ea, eb, e₁, e₂, allocFrame_esp, allocFrame_esp, hsp]) hb₁)
      fun a b ⟨_, _, ⟨e₁, e₂⟩, ea, eb⟩ => by
        subst e₁ e₂ ea eb; exact ⟨fp_args p₁, fp_args p₂⟩) ?_)
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp (F₁ := AfterPad H σ₁) (F₂ := AfterPad H σ₂)
      (RelCT.call Stream.Pad.pad_verified.1 Stream.Pad.pad_verified.2.1
        [] (fpWr σ₁) (fun a b ⟨_, ha', hb'⟩ => ?_))
      fun a b ⟨_, ha', hb'⟩ => ⟨fp_call hr p₁ ha', fp_call hr p₂ hb'⟩) ?_
    · obtain ⟨q1, q2, q3⟩ := fp_pre hr p₁ ha'
      obtain ⟨r1, r2, r3⟩ := fp_pre hr p₂ hb'
      have ew : fpWr σ₂ = fpWr σ₁ := by simp only [fpWr, ha 0 (by decide), hsp]
      rw [ew] at r1 r2 r3
      obtain ⟨x0, x1, x2, x3, x4⟩ := fp_entry p₁.2.2.2.2.2.2.2.2.2.2.2.1 p₁.2.2.2.2.2.2.2.2.2.2.2.2.1 ha'
      obtain ⟨y0, y1, y2, y3, y4⟩ := fp_entry p₂.2.2.2.2.2.2.2.2.2.2.2.1 p₂.2.2.2.2.2.2.2.2.2.2.2.2.1 hb'
      refine ⟨q1, r1, ⟨?_, fun i hi => ?_⟩, q2, q3, r2, r3, by rw [ha'.esp, hb'.esp, hsp]⟩
      · simp only [State.withRegions_gpr, State.callEntry_esp, ha'.esp, hb'.esp, hsp]
      · simp only [arg_withRegions]
        match i, hi with
        | 0, _ => rw [x0, y0, ha 0 (by decide)]
        | 1, _ => rw [x1, y1]
        | 2, _ => rw [x2, y2, ha 1 (by decide)]
        | 3, _ => rw [x3, y3]
        | 4, _ => rw [x4, y4, hsp]
    refine RelCT.seq (Q := fun _ _ => True) (RelCT.wp (F₁ := fsInv H σ₁) (F₂ := fsInv H σ₂)
      (RelCT.taint (A := taint) (τr [.esp]) (fun a b ⟨_, ha', hb'⟩ => agree_regs fun r hr => by
        rw [List.mem_singleton.mp hr, ha'.esp, hb'.esp, hsp]) hb₂)
      fun a b ⟨_, ha', hb'⟩ => ⟨WP.mono (fs_args p₁ ha') fun t h => ⟨a, ha', h⟩,
        WP.mono (fs_args p₂ hb') fun t h => ⟨b, hb', h⟩⟩) ?_
    refine RelCT.call Stream.Squeeze.squeeze_verified.1 Stream.Squeeze.squeeze_verified.2.1
      [] (fsWr H.len σ₁) (fun a b ⟨_, ⟨u₁, hA₁, ha'⟩, ⟨u₂, hA₂, hb'⟩⟩ => ?_)
    obtain ⟨q1, q2, q3⟩ := fs_pre hr hl p₁ hA₁ ha'
    obtain ⟨r1, r2, r3⟩ := fs_pre hr hl p₂ hA₂ hb'
    have ew : fsWr H.len σ₂ = fsWr H.len σ₁ := by
      simp only [fsWr, ha 0 (by decide), ha 2 (by decide), hsp]
    rw [ew] at r1 r2 r3
    obtain ⟨x0, x1, x2, x3, x4, x5⟩ :=
      fs_entry p₁.2.2.2.2.2.2.2.2.2.2.2.1 p₁.2.2.2.2.2.2.2.2.2.2.2.2.1 ha'
    obtain ⟨y0, y1, y2, y3, y4, y5⟩ :=
      fs_entry p₂.2.2.2.2.2.2.2.2.2.2.2.1 p₂.2.2.2.2.2.2.2.2.2.2.2.2.1 hb'
    refine ⟨q1, r1, ⟨?_, fun i hi => ?_⟩, q2, q3, r2, r3, by rw [ha'.esp, hb'.esp, hsp]⟩
    · simp only [State.withRegions_gpr, State.callEntry_esp, ha'.esp, hb'.esp, hsp]
    · simp only [arg_withRegions]
      match i, hi with
      | 0, _ => rw [x0, y0, ha 0 (by decide)]
      | 1, _ => rw [x1, y1]
      | 2, _ => rw [x2, y2]
      | 3, _ => rw [x3, y3, ha 2 (by decide)]
      | 4, _ => rw [x4, y4]
      | 5, _ => rw [x5, y5, hsp]
  exact (hP _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Memory holding SHA-3's `finalize`'s arguments `0x1000, 0, 0x2000` at `0x4004`. -/
def finSatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x400D then 0x20 else 0

def finSat (len : Nat) : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := finSatMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, len⟩, ⟨0x4004, 12⟩]

theorem fin_verified {H : Spec.Sha3.HashFn} (hH : hashSponge H) (hr : H.rate ∈ rates)
    (hl : H.len < 2 ^ 15)
    (hct : ConstantTime isa (finX86 H).pre (finX86 H).pub (finalize H.rate H.len))
    (hsat : ∃ s, (finX86 H).pre s)
    (himp : (finX86 H).Implies (Spec.Sha3.finalizeContract X86.abi H 680)) :
    Verified X86.target (finalize H.rate H.len) (Spec.Sha3.finalizeContract X86.abi H 680) :=
  (show Verified X86.target (finalize H.rate H.len) (finX86 H) from
    ⟨fun _ hs => (fin_correct hH hr hl hs).elim fun t ⟨s', he, h⟩ => ⟨t, s', he, h.1, h.2⟩, hct,
      hsat⟩).of_implies himp

/-- SHA-3's `finalize` for `H`, from the checks the kernel evaluates on its instance. -/
macro "fin_x86" hH:term:max len:term:max : term => `(fin_verified $hH (by decide) (by decide)
  (fin_ct (by decide) (by decide) (by taint_decide) (by taint_decide))
  ⟨finSat $len, by
    have a0 : arg (finSat $len) 0 = 0x1000 := by decide
    have a1 : arg (finSat $len) 1 = 0 := by decide
    have a2 : arg (finSat $len) 2 = 0x2000 := by decide
    have e : argAddr (finSat $len) 0 = 0x4004 := by decide
    simp only [finX86, a0, a1, a2, e]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      by decide⟩ <;>
    · exact Region.disjoint_of_sep (by decide)⟩
  (by contract_implies [Spec.Sha3.finalizeContract, Spec.Sha3.finalizeSig, Spec.Sha3.finalizePre,
      Spec.Sha3.finalizePost, finX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes,
      Spec.Sha3.hashSha3_224, Spec.Sha3.hashSha3_256, Spec.Sha3.hashSha3_384, Spec.Sha3.hashSha3_512]
      [finSat, finSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finSat $len))

theorem finalize_sha3_224 :
    Verified X86.target (finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
      (Spec.Sha3.finalizeContract X86.abi Spec.Sha3.hashSha3_224 680) :=
  fin_x86 VG.Proof.Sha3.Instances.sha3_224_sponge 28

theorem finalize_sha3_256 :
    Verified X86.target (finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
      (Spec.Sha3.finalizeContract X86.abi Spec.Sha3.hashSha3_256 680) :=
  fin_x86 VG.Proof.Sha3.Instances.sha3_256_sponge 32

theorem finalize_sha3_384 :
    Verified X86.target (finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
      (Spec.Sha3.finalizeContract X86.abi Spec.Sha3.hashSha3_384 680) :=
  fin_x86 VG.Proof.Sha3.Instances.sha3_384_sponge 48

theorem finalize_sha3_512 :
    Verified X86.target (finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
      (Spec.Sha3.finalizeContract X86.abi Spec.Sha3.hashSha3_512 680) :=
  fin_x86 VG.Proof.Sha3.Instances.sha3_512_sponge 64

end VG.Proof.Sha3.X86.Instances
