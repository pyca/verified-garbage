module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.ABI
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.Arm.Random

/-!
# The randomized signer's frame on 32-bit ARM

`r11` holds the frame's base `B` (`RF`): its `frameBytes` bytes are writable
and the caller's stack arguments above them readable, all below `2³²`.
Slots and arguments are 32-bit words at offsets from `B` (`slot`). From
the entry state `s₀`, the frame lies 32 bytes above the lowest byte of stack
the signer uses (`rBase`), and the body writes only that stack, `out`,
`scratch` and `used` (`rWrites`), so it reads the caller's arguments and
input bytes as they were on entry (`RReady`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_ldrb wp_strb)

/-- The frame and the arguments above it. -/
structure RF (s : State) (B : Addr) : Prop where
  base : State.addr (s.gpr .r11) = B
  wr : (⟨B, frameBytes⟩ : Region) ∈ s.wr
  args : (⟨off B frameBytes, 28⟩ : Region) ∈ s.rd
  nowrap : B.toNat + frameBytes + 28 ≤ 2 ^ 32

theorem RF.toNat {s : State} {B : Addr} (h : RF s B) : (s.gpr .r11).toNat = B.toNat := by
  rw [← h.base, VG.Proof.X25519.Arm.addr_toNat]

/-- `[r11 + d]`. -/
theorem RF.ea {s : State} {B : Addr} (h : RF s B) {d : Nat} (hd : d < frameBytes + 28) :
    State.addr (s.gpr .r11 + BitVec.ofNat 32 d) = off B d := by
  rw [VG.Arm.addr_add (by have := h.nowrap; have := h.toNat; omega), h.base]

theorem RF.read {s : State} {B : Addr} (h : RF s B) {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions (s.rd ++ s.wr) (off B d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base B hd (by have := h.nowrap; unfold frameBytes at *; omega)⟩

theorem RF.write {s : State} {B : Addr} (h : RF s B) {d n : Nat} (hd : d + n ≤ frameBytes) :
    InRegions s.wr (off B d) n :=
  ⟨_, h.wr, Offset.contains_base B hd (by have := h.nowrap; unfold frameBytes at *; omega)⟩

theorem RF.readArg {s : State} {B : Addr} (h : RF s B) {j : Nat} (hj : j < 7) :
    InRegions (s.rd ++ s.wr) (off B (Random.arg j)) 4 := by
  refine ⟨_, List.mem_append_left _ h.args, ?_⟩
  have e : off B (Random.arg j) = off B frameBytes + BitVec.ofNat 64 (4 * j) := by
    rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  rw [e]
  exact Offset.contains_base _ (by omega) (by omega)

theorem RF.of_rest {ws : List Reg} {s s' : State} {B : Addr} (h : RF s B) (R : Rest ws s s')
    (h11 : .r11 ∉ ws) : RF s' B :=
  ⟨by rw [R.gpr _ h11]; exact h.base, R.wr ▸ h.wr, R.rd ▸ h.args, h.nowrap⟩

/-- The 32-bit word at offset `d` of `B`. -/
abbrev slot (m : Mem) (B : Addr) (d : Nat) : BitVec 32 := m.readW (off B d) 32

theorem slot_write_self (m : Mem) (B : Addr) (d : Nat) (v : BitVec 32) :
    slot (m.writeW (off B d) v) B d = v := Mem.readW_writeW_self32 _ _ _

theorem slot_write_ne (m : Mem) (B : Addr) {o d : Nat} {w : Nat} (v : BitVec w)
    (hsep : d + 4 ≤ o ∨ o + w / 8 ≤ d) (hd : d + 4 ≤ 2 ^ 64) (ho : o + w / 8 ≤ 2 ^ 64) :
    slot (m.writeW (off B o) v) B d = slot m B d :=
  Mem.readW_writeW_sep (Offset.sep B hsep hd ho) (by decide)

/-! ## Where things are -/

/-- The frame's base. -/
abbrev rBase (s₀ : State) : Addr := off (rLow s₀) 32

/-- Where the body may write. -/
def rWrites (s₀ : State) : List Region := [rStack s₀, rOut s₀, rScratch s₀, rUsed s₀]

theorem rBase_off (s₀ : State) (d : Nat) : off (rBase s₀) d = off (rLow s₀) (32 + d) := by
  simp only [rBase, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (A : KeyABI s₀)
include A

theorem rLow_toNat : (rLow s₀).toNat = s₀.sp.toNat - 144 := by
  have := A.stackLow
  rw [rLow, BitVec.toNat_sub, VG.Proof.X25519.Arm.addr_toNat, show (144#64).toNat = 144 from rfl]
  have := s₀.sp.isLt
  omega

theorem off_rLow_toNat {d : Nat} (hd : d ≤ 180) : (off (rLow s₀) d).toNat = (rLow s₀).toNat + d := by
  have := A.stackBound
  have := rLow_toNat A
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem rBase_toNat : (rBase s₀).toNat = s₀.sp.toNat - 112 := by
  rw [rBase, off_rLow_toNat A (by decide), rLow_toNat A]; have := A.stackLow; omega

/-- The caller's stack argument `j`. -/
theorem rBase_arg {j : Nat} (hj : j < 7) : off (rBase s₀) (Random.arg j) = stackArgAddr s₀ j := by
  apply BitVec.eq_of_toNat_eq
  have := A.stackBound
  have := A.stackLow
  rw [rBase_off, off_rLow_toNat A (by unfold Random.arg frameBytes; omega), rLow_toNat A, stackArgAddr,
    VG.Proof.X25519.Arm.addr_toNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * j) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  unfold Random.arg frameBytes; omega

theorem rBase_args : off (rBase s₀) frameBytes = State.addr s₀.sp := by
  have := rBase_arg A (j := 0) (by decide)
  rwa [stackArgAddr, Nat.mul_zero, BitVec.add_zero] at this

/-- The frame reserved on entry. -/
theorem alloc_base : State.addr (s₀.sp - BitVec.ofNat 32 frameBytes) = rBase s₀ := by
  apply BitVec.eq_of_toNat_eq
  have := A.stackLow
  rw [rBase_toNat A, VG.Proof.X25519.Arm.addr_toNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s₀.sp.isLt
  unfold frameBytes; omega

/-- The arguments' 36 bytes are apart from where the body writes. -/
theorem rArgs_apart : ∀ r ∈ rWrites s₀, Region.Disjoint (rArgs s₀) r := by
  intro r hr
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackArgs.symm
  · exact A.outArgs.symm
  · exact A.scratchArgs.symm
  · exact A.usedArgs.symm
end

/-! ## The state the body keeps -/

/-- The frame, the permissions of the entry state with the frame, and memory
changed only where the body may write. -/
structure RReady (s₀ t : State) : Prop where
  rf : RF t (rBase s₀)
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- Registers but `r11` and memory within the stack change. -/
theorem RReady.congr {s₀ t t' : State} {ws : List Reg} (h : RReady s₀ t) (R : Rest ws t t')
    (hm : Frame [rStack s₀] t.mem t'.mem) (h11 : .r11 ∉ ws := by decide) : RReady s₀ t' :=
  ⟨h.rf.of_rest R h11, R.sp.trans h.sp, R.rd.trans h.rd, R.wr.trans h.wr,
    h.frame.trans (hm.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])⟩

theorem RReady.upd {s₀ t t' : State} {d : Reg} {v : BitVec 32} (h : RReady s₀ t) (u : Upd t t' d v)
    (hd : d ≠ .r11 := by decide) : RReady s₀ t' :=
  h.congr (ws := [d]) (u.rest (List.mem_singleton_self _)) (by rw [u.mem]; exact Frame.refl _ _)
    (by simpa using hd.symm)

theorem RReady.fupd {s₀ t t' : State} (h : RReady s₀ t) (u : Fupd t t') : RReady s₀ t' :=
  h.congr (ws := []) (u.rest _) (by rw [u.mem]; exact Frame.refl _ _)

/-- A store to the frame. -/
theorem frame_store (s₀ : State) (m : Mem) {d : Nat} {w : Nat} (hd : d + w / 8 ≤ frameBytes)
    (v : BitVec w) : Frame [rStack s₀] m (m.writeW (off (rBase s₀) d) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) v ?_
  rw [rBase_off]
  exact Offset.contains_base _ (by unfold frameBytes at hd; omega) (by unfold frameBytes at hd; omega)

theorem RReady.mupd {s₀ t t' : State} {d w : Nat} {v : BitVec w} (h : RReady s₀ t)
    (u : Mupd t t' (t.mem.writeW (off (rBase s₀) d) v)) (hd : d + w / 8 ≤ frameBytes) : RReady s₀ t' :=
  h.congr (ws := []) (u.rest _) (by rw [u.mem]; exact frame_store s₀ _ hd v)

/-- The caller's stack arguments. -/
theorem RReady.arg {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) {j : Nat} (hj : j < 7) :
    slot t.mem (rBase s₀) (Random.arg j) = stackArg s₀ j := by
  rw [slot, rBase_arg A hj, stackArg]
  refine h.frame.readW (r := rArgs s₀) ?_ (rArgs_apart A) (by decide)
  rw [stackArgAddr, VG.Arm.addr_add (by have := A.stackBound; omega)]
  exact Offset.contains_base _ (by omega) (by omega)

/-! ## Slots apart from what changed -/

theorem store_in (B : Addr) (m : Mem) {d o n : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hm : (o, n) ∈ rs) (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : d + 4 ≤ 2 ^ 64 := by omega) :
    Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside ((writeW32_outside m B v hb).mono h₁ h₂) hm

theorem store_outs (B : Addr) (m : Mem) {d : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hd : (d, 4) ∈ rs) (hb : d + 4 ≤ 2 ^ 64 := by decide) : Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside (writeW32_outside m B v hb) hd

theorem slot_outs {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 < 2 ^ 64 := by decide) :
    slot m' B d = slot m B d :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    have hi' : i < 4 := hi
    rw [ofs_off B (show d + i < 2 ^ 64 by omega)]; omega

/-! ## Loads and stores of the frame -/

section
variable {s₀ t : State} {is : List Instr} {Q : State → Prop}

/-- `ldr r, [r11, #d]`, a slot of the frame. -/
theorem wp_ld (h : RReady s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (k : ∀ u, Upd t u r (slot t.mem (rBase s₀) d) → WP isa (.block is) u Q) :
    WP isa (.block (ld r d :: is)) t Q :=
  wp_ldr (by unfold frameBytes at hd; omega) (h.rf.ea (by omega)) (h.rf.read hd) k

/-- `ldr r, [r11, #arg j]`, the caller's stack argument `j`. -/
theorem wp_ldArg (A : KeyABI s₀) (h : RReady s₀ t) {r : Reg} {j : Nat} (hj : j < 7)
    (k : ∀ u, Upd t u r (stackArg s₀ j) → WP isa (.block is) u Q) :
    WP isa (.block (ld r (Random.arg j) :: is)) t Q :=
  wp_ldr (by unfold Random.arg frameBytes; omega) (h.rf.ea (by unfold Random.arg; omega)) (h.rf.readArg hj)
    fun u v => k u (by rw [← h.arg A hj]; exact v)

/-- `str r, [r11, #d]`, a slot of the frame. -/
theorem wp_st (h : RReady s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (k : ∀ u, Mupd t u (t.mem.writeW (off (rBase s₀) d) (t.gpr r)) → RReady s₀ u → WP isa (.block is) u Q) :
    WP isa (.block (st r d :: is)) t Q :=
  wp_str (by unfold frameBytes at hd; omega) (h.rf.ea (by omega)) (h.rf.write hd) fun u v => k u v (h.mupd v hd)

/-- `str r, [r11, #d]`, keeping the flags. -/
theorem wp_stF (h : RReady s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (k : ∀ u, Mupd t u (t.mem.writeW (off (rBase s₀) d) (t.gpr r)) → RReady s₀ u → u.z = t.z → u.c = t.c →
      WP isa (.block is) u Q) :
    WP isa (.block (st r d :: is)) t Q := by
  have e := h.rf.ea (d := d) (by omega)
  refine VG.Proof.X25519.Arm.WP.cons (exec_str (by unfold frameBytes at hd; omega) (by rw [e]; exact h.rf.write hd)) ?_
  rw [e]
  exact k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ (h.mupd ⟨rfl, rfl, rfl, rfl, rfl⟩ hd) rfl rfl

end

/-! ## Bytes of the caller's buffers -/

/-- `bs` at `p`: readable bytes below `2³²`. -/
structure BytesIn (s : State) (p : BitVec 32) (bs : List Byte) : Prop where
  fit : p.toNat + bs.length ≤ 2 ^ 32
  rd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1
  val : ∀ i (h : i < bs.length), s.mem (State.addr p + BitVec.ofNat 64 i) = bs[i]

theorem BytesIn.drop {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (j : Nat)
    (hj : j ≤ bs.length) : BytesIn s (p + BitVec.ofNat 32 j) (bs.drop j) := by
  have hfit := h.fit
  have e : ∀ i, j + i < bs.length → State.addr (p + BitVec.ofNat 32 j) + BitVec.ofNat 64 i =
      State.addr p + BitVec.ofNat 64 (j + i) := fun i hi => by
    rw [VG.Arm.addr_add (by omega), Offset.add_add]
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_drop]
    by_cases hjl : j = bs.length
    · rw [hjl, Nat.sub_self, Nat.add_zero]; exact Nat.le_of_lt (BitVec.isLt _)
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega
  · rw [List.length_drop] at hi
    rw [e i (by omega)]; exact h.rd _ (by omega)
  · rw [List.length_drop] at hi
    rw [e i (by omega), h.val _ (by omega), List.getElem_drop]

theorem BytesIn.take {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (n : Nat) :
    BytesIn s p (bs.take n) := by
  refine ⟨by rw [List.length_take]; have := h.fit; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_take] at hi; exact h.rd i (by omega)
  · rw [List.length_take] at hi; rw [List.getElem_take]; exact h.val i (by omega)

theorem BytesIn.congr {s t : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : BytesIn t p bs :=
  ⟨h.fit, fun i hi => by rw [hr, hw]; exact h.rd i hi, fun i hi => by rw [hm]; exact h.val i hi⟩

/-- Bytes the body reads, apart from where it writes. -/
theorem RReady.bytes {s₀ t : State} (h : RReady s₀ t) {p : BitVec 32} {n : Nat}
    (hr : (⟨State.addr p, n⟩ : Region) ∈ s₀.rd) (hfit : p.toNat + n ≤ 2 ^ 32)
    (hd : ∀ r ∈ rWrites s₀, Region.Disjoint ⟨State.addr p, n⟩ r) :
    BytesIn t p (Spec.Rsa.bytesAt s₀.mem (State.addr p) n) := by
  refine ⟨by rw [rBytes_length]; exact hfit, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rBytes_length] at hi
    exact ⟨_, List.mem_append_left _ (h.rd ▸ hr), Offset.contains_base _ (by omega) (by omega)⟩
  · rw [rBytes_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.frame.bytes (R := ⟨State.addr p, n⟩) hd (show n ≤ 2 ^ 64 by omega) hi

theorem RReady.rand {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) :
    BytesIn t (stackArg s₀ 3) (rInput s₀).rand := by
  refine h.bytes (by rw [A.rd]; simp) A.randBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackRand.symm
  · exact A.outRand.symm
  · exact A.randScratch
  · exact A.usedRand.symm

theorem RReady.key {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) :
    BytesIn t (s₀.gpr .r3) (rInput s₀).key := by
  refine h.bytes (by rw [A.rd]; simp) A.keyBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

theorem RReady.q {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) : BytesIn t (rQ s₀) (rQBytes s₀) := by
  have hk := h.key A
  have hp : (stackArg s₀ 1).toNat ≤ (rInput s₀).key.length := by
    simp only [rInput, rBytes_length, A.keyLength]; omega
  have := (hk.drop _ hp).take (rInput s₀).qLen
  simpa only [rQ, rQBytes, rInput, BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

end VG.Proof.Dsa.Arm.Key
