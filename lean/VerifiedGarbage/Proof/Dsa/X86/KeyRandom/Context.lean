module

public import VerifiedGarbage.Proof.Dsa.X86.RandomScan
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.ABI
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Frame
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.RandomContext

/-!
# The key generator's context (x86)

From the entry state `s₀` (`KeyABI`): the 144 bytes of stack below
the return address, from `rLow s₀`, hold the callee's return address and
stack (24 bytes) and the frame (`rBase s₀`, `KeyRandom.frameBytes`). The body writes
only that stack, `out`, `scratch` and `used` (`rWrites`), so it reads the
caller's arguments and input bytes as they were on entry (`Ready`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-! ## A frame of stack -/

/-- The state after reserving `bytes` bytes of stack. -/
def allocated (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 bytes) with
    wr := ⟨(s.gpr .esp - BitVec.ofNat 32 bytes).setWidth 64, bytes⟩ :: s.wr }

/-- The state after releasing them. -/
def freed (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp + BitVec.ofNat 32 bytes) with wr := s.wr.tail }

/-- A frame of `bytes` bytes of stack around a body that never writes `esp`. -/
theorem WP.alloc {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0) (hsp : bytes ≤ (s.gpr .esp).toNat) (hb : NoSp body)
    (h : WP isa body (allocated bytes s) fun s₂ => Q (freed bytes s₂)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := h
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hb he
  have ha : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, hn.1, hn.2.1, hn.2.2, hsp, and_self, ite_true]
    rfl
  have hf : isa.pop (.free bytes) (allocated bytes s) s₂ = some (freed bytes s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨hn.1, hn.2.1, hn.2.2, hp, hw, ?_⟩
    rfl
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

theorem allocated_esp (n : Nat) (s : State) : (allocated n s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 n :=
  RegUpd.gpr_setReg_self s .esp _
theorem allocated_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (allocated n s).gpr r = s.gpr r :=
  RegUpd.gpr_setReg_of_ne s _ h
theorem allocated_wr (n : Nat) (s : State) :
    (allocated n s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 n).setWidth 64, n⟩ :: s.wr := rfl
theorem freed_esp (n : Nat) (s : State) : (freed n s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 n :=
  RegUpd.gpr_setReg_self s .esp _
theorem freed_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (freed n s).gpr r = s.gpr r :=
  RegUpd.gpr_setReg_of_ne s _ h

/-! ## Where things are -/

/-- The lowest byte of the stack the callee uses, 144 bytes below its
return address. -/
def rLow (s₀ : State) : Addr := (s₀.gpr .esp).setWidth 64 - 144#64

/-- The frame's base. -/
def rBase (s₀ : State) : Addr := off (rLow s₀) 24

def rStack (s₀ : State) : Region := ⟨rLow s₀, 144⟩
def rOut (s₀ : State) : Region := argRegion s₀ 0 (X86.arg s₀ 1).toNat
def rUsed (s₀ : State) : Region := argRegion s₀ 2 8
def rScratch (s₀ : State) : Region := argRegion s₀ 9 ((X86.arg s₀ 10).toNat * 8)

/-- Where the body may write. -/
def rWrites (s₀ : State) : List Region := [rStack s₀, rOut s₀, rScratch s₀, rUsed s₀]

/-- What the specification reads. -/
def rInput (s₀ : State) : VG.Proof.Dsa.RandomSignInput where
  pLen := (X86.arg s₀ 5).toNat
  qLen := (X86.arg s₀ 6).toNat
  key := Spec.Rsa.bytesAt s₀.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat
  digest := []
  rand := Spec.Rsa.bytesAt s₀.mem (argumentPointer s₀ 7) (X86.arg s₀ 8).toNat

/-- q's bytes, and their address. -/
def rQBytes (s₀ : State) : List Byte := ((rInput s₀).key.drop (rInput s₀).pLen).take (rInput s₀).qLen
def rQ (s₀ : State) : BitVec 32 := X86.arg s₀ 3 + X86.arg s₀ 5

/-- q's significant bytes, and the first of them. -/
abbrev rWidth (s₀ : State) : Nat := (VG.Proof.Dsa.significant (rQBytes s₀)).1
abbrev rLead (s₀ : State) : Byte := (VG.Proof.Dsa.significant (rQBytes s₀)).2

theorem rQ_decode (s₀ : State) :
    Spec.Dsa.decodeBE (rQBytes s₀) =
      (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q := rfl

theorem rBase_off (s₀ : State) (d : Nat) : off (rBase s₀) d = off (rLow s₀) (24 + d) := by
  simp only [rBase, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (A : KeyABI s₀)
include A

theorem rLow_toNat : (rLow s₀).toNat = (s₀.gpr .esp).toNat - 144 := by
  have := A.stackLow
  have := (s₀.gpr .esp).isLt
  rw [rLow, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := (s₀.gpr .esp).toNat) (by omega)]
  omega

theorem rLow_fit {d : Nat} (hd : d ≤ 192) : (rLow s₀).toNat + d ≤ 2 ^ 32 := by
  have := A.stackBound; rw [rLow_toNat A]; omega

theorem off_rLow_toNat {d : Nat} (hd : d ≤ 192) : (off (rLow s₀) d).toNat = (rLow s₀).toNat + d := by
  have := rLow_fit A hd
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem argAddr_eq {j : Nat} (hj : j < 11) : argAddr s₀ j = off (rLow s₀) (148 + 4 * j) := by
  apply BitVec.eq_of_toNat_eq
  have := A.stackBound
  rw [off_rLow_toNat A (by omega), rLow_toNat A, argAddr, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 + 4 * j) (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  have := A.stackLow
  omega

theorem rBase_arg {j : Nat} (hj : j < 11) : off (rBase s₀) (argOff j) = argAddr s₀ j := by
  rw [rBase_off, argAddr_eq A hj, show 24 + argOff j = 148 + 4 * j by unfold argOff KeyRandom.frameBytes; omega]

/-- The frame reserved on entry. -/
theorem alloc_base : (s₀.gpr .esp - BitVec.ofNat 32 KeyRandom.frameBytes).setWidth 64 = rBase s₀ := by
  have := A.stackLow
  rw [show KeyRandom.frameBytes = 120 from rfl, Taint.sub_setWidth (by omega), rBase, rLow, off,
    Offset.sub_ofNat_eq _ (show 120 ≤ 144 by decide)]

theorem alloc_rf : RF (allocated KeyRandom.frameBytes s₀) (rBase s₀) := by
  refine ⟨by rw [allocated_esp]; exact alloc_base A, ?_, ?_, ?_⟩
  · rw [allocated_wr, alloc_base A]; exact List.mem_cons_self
  · rw [allocated_wr, rBase_arg A (by decide), A.wr]; simp
  · have := rLow_fit A (d := 192) (by decide)
    rw [rBase, off_rLow_toNat A (by decide)]; unfold argOff KeyRandom.frameBytes; omega

/-- The arguments' 44 bytes are apart from where the body writes. -/
theorem args_apart : ∀ r ∈ rWrites s₀, Region.Disjoint ⟨argAddr s₀ 0, 44⟩ r := by
  intro r hr
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [argAddr_eq A (by decide)]
    exact Offset.disjoint_base (rLow s₀) (by decide) (by decide)
  · exact A.outArgs.symm
  · exact A.scratchArgs.symm
  · exact A.usedArgs.symm

/-- The return address on entry is apart from the buffers. -/
theorem stack_apart_key : (rStack s₀).Disjoint (argRegion s₀ 3 (X86.arg s₀ 4).toNat) := A.stackKey
end

theorem rBytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-! ## The state the body keeps -/

/-- The frame, the permissions of the entry state with the frame, and memory
changed only where the body may write. -/
structure Ready (s₀ t : State) : Prop where
  rf : RF t (rBase s₀)
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, KeyRandom.frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

theorem alloc_ready {s₀ : State} (A : KeyABI s₀) : Ready s₀ (allocated KeyRandom.frameBytes s₀) :=
  ⟨alloc_rf A, rfl, by rw [allocated_wr, alloc_base A], Frame.refl _ _⟩

/-- Registers but `esp` and memory within the stack change. -/
theorem Ready.congr {s₀ t t' : State} {rs : List Reg} (h : Ready s₀ t) (hk : Keeps rs t t')
    (hm : Frame [rStack s₀] t.mem t'.mem) (hsp : .esp ∉ rs := by decide) : Ready s₀ t' :=
  ⟨h.rf.of_keeps hk hsp, hk.2.1.trans h.rd, hk.2.2.trans h.wr,
    h.frame.trans (hm.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])⟩

theorem Ready.upd {s₀ t t' : State} {d : Reg} {v : BitVec 32} (h : Ready s₀ t) (u : Upd t t' d v)
    (hd : d ≠ .esp) : Ready s₀ t' :=
  h.congr (rs := [d]) u.keeps (by rw [u.mem]; exact Frame.refl _ _) (by simpa using hd.symm)

theorem Ready.fupd {s₀ t t' : State} (h : Ready s₀ t) (u : Fupd t t') : Ready s₀ t' :=
  h.congr (rs := []) (u.keeps _) (by rw [u.mem]; exact Frame.refl _ _)

/-- A store to the frame. -/
theorem frame_store (s₀ : State) (m : Mem) {d : Nat} (hd : d + 4 ≤ KeyRandom.frameBytes)
    (v : BitVec 32) : Frame [rStack s₀] m (m.writeW (off (rBase s₀) d) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) v ?_
  rw [rBase_off]
  have : KeyRandom.frameBytes = 120 := rfl
  exact Offset.contains_base _ (by omega) (by omega)

/-- A byte store to the frame. -/
theorem frame_store8 (s₀ : State) (m : Mem) {d : Nat} (hd : d + 1 ≤ KeyRandom.frameBytes)
    (v : BitVec 8) : Frame [rStack s₀] m (m.writeW (off (rBase s₀) d) v) := by
  refine Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) v ?_
  rw [rBase_off]
  have : KeyRandom.frameBytes = 120 := rfl
  exact Offset.contains_base _ (by omega) (by omega)

/-- The caller's arguments. -/
theorem Ready.arg {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {j : Nat} (hj : j < 11) :
    t.mem.readW (off (rBase s₀) (argOff j)) 32 = X86.arg s₀ j := by
  rw [rBase_arg A hj, X86.arg]
  refine h.frame.readW (r := ⟨argAddr s₀ j, 4⟩) ?_ (fun r hr => (args_apart A r hr).sub_left ?_) (by decide)
  · exact Offset.contains_base _ (show 0 + 4 ≤ 4 by decide) (by decide) |> fun h => by
      simpa only [BitVec.add_zero] using h
  · rw [argAddr_eq A hj, argAddr_eq A (by decide)]
    exact Offset.sub _ (by omega) (by omega)

theorem Ready.argSrc {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {j : Nat} (hj : j < 11) :
    readSrc t (.mem (KeyRandom.arg j)) = some (X86.arg s₀ j) := by
  rw [h.rf.readArgSrc hj, h.arg A hj]

/-- Bytes the body reads, apart from where it writes. -/
theorem Ready.bytes {s₀ t : State} (h : Ready s₀ t) {p : BitVec 32} {n : Nat}
    (hr : (⟨p.setWidth 64, n⟩ : Region) ∈ s₀.rd) (hfit : p.toNat + n ≤ 2 ^ 32)
    (hd : ∀ r ∈ rWrites s₀, Region.Disjoint ⟨p.setWidth 64, n⟩ r) :
    BytesIn t p (Spec.Rsa.bytesAt s₀.mem (p.setWidth 64) n) := by
  refine ⟨by rw [rBytes_length]; exact hfit, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rBytes_length] at hi
    exact ⟨_, List.mem_append_left _ (h.rd ▸ hr), Offset.contains_base _ (by omega) (by omega)⟩
  · rw [rBytes_length] at hi
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.frame.bytes (R := ⟨p.setWidth 64, n⟩) hd (show n ≤ 2 ^ 64 by omega) hi

theorem Ready.rand {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    BytesIn t (X86.arg s₀ 7) (rInput s₀).rand := by
  refine h.bytes (by rw [A.rd]; simp) A.randBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackRand.symm
  · exact A.outRand.symm
  · exact A.randScratch
  · exact A.usedRand.symm

theorem Ready.key {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    BytesIn t (X86.arg s₀ 3) (rInput s₀).key := by
  refine h.bytes (by rw [A.rd]; simp) A.keyBound fun r hr => ?_
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

theorem BytesIn.take {s : State} {p : BitVec 32} {bs : List Byte} (h : BytesIn s p bs) (n : Nat) :
    BytesIn s p (bs.take n) := by
  refine ⟨by rw [List.length_take]; have := h.fit; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [List.length_take] at hi; exact h.rd i (by omega)
  · rw [List.length_take] at hi; rw [List.getElem_take]; exact h.val i (by omega)

theorem rQBytes_length {s₀ : State} (A : KeyABI s₀) : (rQBytes s₀).length = (X86.arg s₀ 6).toNat := by
  simp only [rQBytes, rInput, List.length_take, List.length_drop, rBytes_length, A.keyLength]
  omega

theorem rQBytes_le {s₀ : State} (A : KeyABI s₀) : (rQBytes s₀).length ≤ 32 := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega

theorem rQBytes_pos {s₀ : State} (A : KeyABI s₀) : 0 < (rQBytes s₀).length := by
  rw [rQBytes_length A]; have := A.lengths; unfold Spec.Dsa.lengthsValid at this; omega

theorem Ready.q {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) : BytesIn t (rQ s₀) (rQBytes s₀) := by
  have hk := h.key A
  have hp : (X86.arg s₀ 5).toNat ≤ (rInput s₀).key.length := by
    simp only [rInput, rBytes_length, A.keyLength]; omega
  have := (hk.drop _ hp).take (rInput s₀).qLen
  simpa only [rQ, rQBytes, rInput, BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

end VG.Proof.Dsa.X86.KeyRandom
