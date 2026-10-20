module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Mask

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Prepare
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86.RandomContext

/-!
# Copying a draw into the scalar (x86)

`copy` copies the `width` bytes of the tape from `used` on to the last
`width` bytes of the `q_len`-byte scalar, the first masked (`copied`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- `esp + c` as an address in the frame. -/
theorem RF.ptr {s : State} {B : Addr} (hf : RF s B) {c : Nat} (hc : c < argOff 11) :
    (s.gpr .esp + BitVec.ofNat 32 c).setWidth 64 = off B c := by
  rw [← hf.esp]
  exact addr_eq (by have := hf.nowrap; have := hf.esp_toNat; omega)

/-- `[r + 0]`. -/
theorem ea_at0 (s : State) (r : Reg) : s.ea (at_ r 0) = (s.gpr r).setWidth 64 := by
  change (s.gpr r + BitVec.ofNat 32 0).setWidth 64 = _
  rw [BitVec.add_zero]

theorem ptr_add {p : BitVec 32} {i : Nat} (h : p.toNat + i < 2 ^ 32) :
    (p + BitVec.ofNat 32 i).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 i := addr_eq h

/-- A byte of the frame is writable. -/
theorem RF.write1 {s : State} {B : Addr} (hf : RF s B) {d : Nat} (hd : d < KeyRandom.frameBytes) :
    InRegions s.wr (off B d) 1 := hf.write (by omega)

/-- What the scalar's byte `i` from the draw's place becomes: the first byte
masked. -/
def copied (bs : List Byte) (mask : BitVec 32) (i : Nat) : Byte :=
  if i = 0 then ((bs.getD 0 0).setWidth 32 &&& mask).setWidth 8 else bs.getD i 0

/-- The copy after its first `k ≥ 1` bytes. `d` is the draw's place in the
frame, `p` its source. -/
structure CopyInv (s₀ t₀ : State) (p : BitVec 32) (d : Nat) (bs : List Byte) (mask : BitVec 32)
    (k : Nat) (t : State) : Prop where
  ready : Ready s₀ t
  esi : t.gpr .esi = p + BitVec.ofNat 32 k
  edx : t.gpr .edx = t.gpr .esp + BitVec.ofNat 32 (d + k)
  ecx : t.gpr .ecx = BitVec.ofNat 32 (bs.length - k)
  bytes : ∀ i < k, t.mem (off (rBase s₀) (d + i)) = copied bs mask i
  out : Outside (rBase s₀) d bs.length t₀.mem t.mem
  keeps : Keeps [.eax, .ecx, .edx, .esi] t₀ t

theorem byte_setWidth (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- One byte after the first. -/
theorem copyByte_ok {s₀ t₀ t : State} {p : BitVec 32} {d : Nat} {bs : List Byte} {mask : BitVec 32}
    {k : Nat} (hin : BytesIn t p bs) (hd : d + bs.length ≤ KeyRandom.frameBytes) (hk : k < bs.length)
    (I : CopyInv s₀ t₀ p d bs mask k t) (hk0 : 1 ≤ k) :
    WP isa (.block copyByte) t fun u => CopyInv s₀ t₀ p d bs mask (k + 1) u ∧
      u.zf = some (decide (bs.length - (k + 1) = 0)) := by
  have hfit := hin.fit
  have hrf := I.ready.rf
  have hF : KeyRandom.frameBytes = 120 := rfl
  unfold copyByte
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 k)
    (by rw [ea_at0, I.esi]; exact ptr_add (by omega)) (hin.rd k hk) fun u₁ v₁ _ _ => ?_
  rw [hin.val k hk] at v₁
  have he : u₁.ea (at_ .edx 0) = off (rBase s₀) (d + k) := by
    rw [ea_at0, v₁.other _ (by decide), I.edx]
    exact hrf.ptr (by unfold argOff KeyRandom.frameBytes at *; omega)
  have f₁ := hrf.of_keeps v₁.keeps
  refine wp_store8 he (f₁.write1 (by omega)) fun u₂ m₂ => wp_addi fun u₃ v₃ => wp_addi fun u₄ v₄ =>
    wp_subi fun u₅ v₅ _ z₅ => WP.block_nil ?_
  have hv : (u₁.gpr (Reg8.al).reg).setWidth 8 = bs[k] := by
    show (u₁.gpr .eax).setWidth 8 = _; rw [v₁.gpr, byte_setWidth]
  rw [hv] at m₂
  have kk : Keeps [.eax, .ecx, .edx, .esi] t u₅ :=
    ((((v₁.keeps.mono (by decide)).trans (m₂.keeps _)).trans (v₃.keeps.mono (by decide))).trans
      (v₄.keeps.mono (by decide))).trans (v₅.keeps.mono (by decide))
  have mem₅ : u₅.mem = t.mem.writeW (off (rBase s₀) (d + k)) bs[k] := by
    rw [v₅.mem, v₄.mem, v₃.mem, m₂.mem, v₁.mem]
  have esp₅ : u₅.gpr .esp = t.gpr .esp := kk.1 _ (by decide)
  have hb : bs.length < 2 ^ 32 := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, I.keeps.trans kk⟩, ?_⟩
  · exact I.ready.congr kk (by rw [mem₅]; exact frame_store8 s₀ _ (by omega) _)
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, m₂.gpr, v₁.other _ (by decide), I.esi,
      Offset.add_ofNat_add_one]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide), m₂.gpr, v₁.other _ (by decide), I.edx,
      esp₅, Offset.add_ofNat_add_one]; rfl
  · rw [v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide), m₂.gpr, v₁.other _ (by decide), I.ecx,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  · intro i hi
    rw [mem₅]
    by_cases hik : i = k
    · subst hik
      rw [writeW8_self]
      simp only [copied, show i ≠ 0 by omega, ite_false, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk, Option.getD_some]
    · rw [writeW8_outside _ _ (d := d + k) _ (by omega) _ (by
        rw [ofs_off0 _ (by omega)]; omega)]
      exact I.bytes i (by omega)
  · rw [mem₅]
    exact I.out.trans ((writeW8_outside _ _ (d := d + k) _ (by omega)).mono (by omega) (by omega))
  · rw [z₅, v₄.other _ (by decide), v₃.other _ (by decide), m₂.gpr, v₁.other _ (by decide), I.ecx,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- The bytes after the first. -/
theorem copyLoop_ok {s₀ t₀ t : State} {p : BitVec 32} {d : Nat} {bs : List Byte} {mask : BitVec 32}
    {k : Nat} (hin : ∀ u, Ready s₀ u → BytesIn u p bs) (hd : d + bs.length ≤ KeyRandom.frameBytes)
    (hk : k < bs.length) (hk0 : 1 ≤ k) (I : CopyInv s₀ t₀ p d bs mask k t) :
    WP isa (.loop (.block copyByte) .ne) t fun u => CopyInv s₀ t₀ p d bs mask bs.length u := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) =>
      ∃ j, n = bs.length - j ∧ 1 ≤ j ∧ j < bs.length ∧ CopyInv s₀ t₀ p d bs mask j u)
    (fun n u hu => ?_) (bs.length - k) t ⟨k, rfl, hk0, hk, I⟩
  obtain ⟨j, hn, hj0, hj, J⟩ := hu
  refine WP.mono (copyByte_ok (hin u J.ready) hd hj J hj0) fun v ⟨J', z⟩ => ?_
  by_cases he : bs.length - (j + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rw [show bs.length = j + 1 by omega]; exact J'
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false],
      bs.length - (j + 1), by omega, j + 1, rfl, by omega, by omega, J'⟩

/-- The draw at `used`, as bytes of the frame reads them. -/
theorem Ready.draw {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : used ≤ (rInput s₀).rand.length) (w : Nat) :
    BytesIn t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (((rInput s₀).rand.drop used).take w) :=
  ((h.rand A).drop used hu).take w

/-- The draw's place in the scalar, and its source. -/
abbrev drawPlace (s₀ : State) : Nat := oNonce + ((rQBytes s₀).length - rWidth s₀)
abbrev drawBytes (s₀ : State) (used : Nat) : List Byte := ((rInput s₀).rand.drop used).take (rWidth s₀)

/-- The draw's source, count and place. -/
theorem copyHeader_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)) :
    WP isa (.block copyHeader) t fun u => Ready s₀ u ∧ u.mem = t.mem ∧ Keeps [.eax, .ecx, .edx, .esi] t u ∧
      u.gpr .esi = X86.arg s₀ 7 + BitVec.ofNat 32 used ∧ u.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) ∧
      u.gpr .edx = u.gpr .esp + BitVec.ofNat 32 (drawPlace s₀) := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold copyHeader
  refine wp_movS (h.argSrc A (j := 7) (by decide)) fun t₁ u₁ _ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_addS (v := BitVec.ofNat 32 used) (by rw [h₁.rf.readSlot (by decide), u₁.mem]; exact congrArg some hu) fun t₂ u₂ _ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  refine wp_movS (v := BitVec.ofNat 32 (rWidth s₀)) (by rw [h₂.rf.readSlot (by decide), u₂.mem, u₁.mem]; exact congrArg some hw) fun t₃ u₃ _ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  refine wp_movS rfl fun t₄ u₄ _ => ?_
  have h₄ := h₃.upd u₄ (by decide)
  refine wp_addi fun t₅ u₅ => ?_
  have h₅ := h₄.upd u₅ (by decide)
  refine wp_addS (h₅.argSrc A (j := 6) (by decide)) fun t₆ u₆ _ => ?_
  have h₆ := h₅.upd u₆ (by decide)
  refine wp_sub fun t₇ u₇ _ => WP.block_nil ?_
  have h₇ := h₆.upd u₇ (by decide)
  have k₇ : Keeps [.eax, .ecx, .edx, .esi] t t₇ :=
    ((((((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))).trans
      (u₄.keeps.mono (by decide))).trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))).trans
      (u₇.keeps.mono (by decide))
  have m₇ : t₇.mem = t.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have esp₇ : t₇.gpr .esp = t.gpr .esp := k₇.1 _ (by decide)
  have esi₇ : t₇.gpr .esi = X86.arg s₀ 7 + BitVec.ofNat 32 used := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr]
  have ecx₇ : t₇.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have edx₇ : t₇.gpr .edx = t₇.gpr .esp + BitVec.ofNat 32 (drawPlace s₀) := by
    have ecx₃ : t₃.gpr .ecx = BitVec.ofNat 32 (rWidth s₀) := u₃.gpr
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₆.other .ecx (by decide), u₅.other .ecx (by decide),
      u₄.other .ecx (by decide), ecx₃, esp₇, u₃.other .esp (by decide), u₂.other .esp (by decide),
      u₁.other .esp (by decide),
      show X86.arg s₀ 6 = BitVec.ofNat 32 (rQBytes s₀).length by rw [hqn, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      Offset.add_add, add_ofNat_sub32 _ (by omega) (by unfold oNonce; omega)]
    unfold drawPlace; congr 2; omega
  exact ⟨h₇, m₇, k₇, esi₇, ecx₇, edx₇⟩

/-- The draw's header and its first byte. -/
theorem copyInit_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hm : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa (.block copyInit) t fun u => CopyInv s₀ t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (drawPlace s₀)
      (drawBytes s₀ used) (maskValue (rLead s₀).toNat) 1 u ∧ u.zf = some (decide (rWidth s₀ - 1 = 0)) := by
  have hF : KeyRandom.frameBytes = 120 := rfl
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hlen : (drawBytes s₀ used).length = rWidth s₀ := by
    simp only [drawBytes, List.length_take, List.length_drop]; omega
  have hin := fun u (hr : Ready s₀ u) => hr.draw A (show used ≤ _ by omega) (rWidth s₀)
  have hd : drawPlace s₀ + (drawBytes s₀ used).length ≤ KeyRandom.frameBytes := by
    rw [hlen]; unfold drawPlace oNonce; omega
  unfold copyInit
  refine WP.block_append (WP.mono (copyHeader_ok A h hu hw) fun t₇ ⟨h₇, m₇, k₇, esi₇, ecx₇, edx₇⟩ => ?_)
  unfold copyFirst
  -- The first byte.
  have hb₀ := (hin t₇ h₇).rd 0 (by rw [hlen]; omega)
  rw [BitVec.add_zero] at hb₀
  refine wp_load8 (a := (X86.arg s₀ 7 + BitVec.ofNat 32 used).setWidth 64)
    (by rw [ea_at0, esi₇]) hb₀ fun t₈ u₈ _ _ => ?_
  have hv₈ := (hin t₇ h₇).val 0 (by rw [hlen]; omega)
  rw [BitVec.add_zero] at hv₈
  rw [hv₈] at u₈
  have h₈ := h₇.upd u₈ (by decide)
  refine wp_logicS (.inl rfl) (v := maskValue (rLead s₀).toNat) (by rw [h₈.rf.readSlot (by decide), u₈.mem, m₇]; exact congrArg some hm) fun t₉ u₉ => ?_
  simp only [↓reduceIte] at u₉
  have h₉ := h₈.upd u₉ (by decide)
  have he : t₉.ea (at_ .edx 0) = off (rBase s₀) (drawPlace s₀ + 0) := by
    rw [ea_at0, u₉.other _ (by decide), u₈.other _ (by decide), edx₇]
    exact h₇.rf.ptr (by unfold argOff drawPlace oNonce; omega)
  refine wp_store8 he (h₉.rf.write1 (by unfold drawPlace oNonce; omega)) fun t₁₀ m₁₀ =>
    wp_addi fun t₁₁ u₁₁ => wp_addi fun t₁₂ u₁₂ => wp_subi fun t₁₃ u₁₃ _ z₁₃ => WP.block_nil ?_
  have k₁₃ : Keeps [.eax, .ecx, .edx, .esi] t₇ t₁₃ :=
    ((((u₈.keeps.mono (by decide)).trans (u₉.keeps.mono (by decide))).trans (m₁₀.keeps _)).trans
      ((u₁₁.keeps.mono (by decide)).trans (u₁₂.keeps.mono (by decide)))).trans (u₁₃.keeps.mono (by decide))
  have mem₁₃ : t₁₃.mem = t.mem.writeW (off (rBase s₀) (drawPlace s₀ + 0))
      ((((drawBytes s₀ used)[0]'(by rw [hlen]; omega)).setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8) := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, u₉.mem, u₈.mem, m₇, show (Reg8.al).reg = Reg.eax from rfl,
      u₉.gpr, u₈.gpr]
  have hout : Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem t₁₃.mem := by
    rw [mem₁₃]
    exact (writeW8_outside t.mem (rBase s₀) (d := drawPlace s₀ + 0)
      ((((drawBytes s₀ used)[0]'(by rw [hlen]; omega)).setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8)
      (by unfold drawPlace oNonce; omega)).mono (o' := drawPlace s₀) (n' := rWidth s₀)
      (by unfold drawPlace oNonce; omega) (by unfold drawPlace oNonce; omega)
  have I₁ : CopyInv s₀ t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (drawPlace s₀) (drawBytes s₀ used)
      (maskValue (rLead s₀).toNat) 1 t₁₃ := by
    refine ⟨h₇.congr k₁₃ (by rw [mem₁₃, m₇]; exact frame_store8 s₀ _ (by unfold drawPlace oNonce; omega) _),
      ?_, ?_, ?_, ?_, ?_, k₇.trans k₁₃⟩
    · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), esi₇]; rfl
    · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), edx₇, k₁₃.1 .esp (by decide), Offset.add_ofNat_add_one]
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), ecx₇, hlen, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        sub_ofNat hw1]
    · intro i hi
      rw [show i = 0 by omega, mem₁₃, writeW8_self]
      simp only [copied, ↓reduceIte, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show 0 < (drawBytes s₀ used).length by rw [hlen]; omega), Option.getD_some]
    · rw [hlen]; exact hout
  have z₁ : t₁₃.zf = some (decide (rWidth s₀ - 1 = 0)) := by
    rw [z₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), ecx₇, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  exact ⟨I₁, z₁⟩

theorem copy_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) {used : Nat}
    (hu : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used)
    (hw : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀))
    (hm : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa copy t fun u => Ready s₀ u ∧
      (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧
      Keeps [.eax, .ecx, .edx, .esi] t u := by
  have hF : KeyRandom.frameBytes = 120 := rfl
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hlen : (drawBytes s₀ used).length = rWidth s₀ := by
    simp only [drawBytes, List.length_take, List.length_drop]; omega
  have hin := fun u (hr : Ready s₀ u) => hr.draw A (show used ≤ _ by omega) (rWidth s₀)
  have hd : drawPlace s₀ + (drawBytes s₀ used).length ≤ KeyRandom.frameBytes := by
    rw [hlen]; unfold drawPlace oNonce; omega
  have fin : ∀ u, CopyInv s₀ t (X86.arg s₀ 7 + BitVec.ofNat 32 used) (drawPlace s₀) (drawBytes s₀ used)
      (maskValue (rLead s₀).toNat) (rWidth s₀) u →
      Ready s₀ u ∧ (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .esi] t u :=
    fun u J => ⟨J.ready, J.bytes, hlen ▸ J.out, J.keeps⟩
  unfold copy
  refine WP.seq (WP.mono (copyInit_ok A h hu hw hm hfull hw1) fun t₁₃ ⟨I₁, z₁⟩ => ?_)
  unfold copyRest
  by_cases h1 : rWidth s₀ = 1
  · refine WP.ite false (by simp only [eval, z₁, h1, Nat.sub_self, decide_true, Option.map_some,
      Bool.not_true]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil (fin _ ?_))
    rw [h1]; exact I₁
  · refine WP.ite true (by simp only [eval, z₁, show rWidth s₀ - 1 ≠ 0 by omega, decide_false,
      Option.map_some, Bool.not_false]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    exact WP.mono (copyLoop_ok hin hd (by rw [hlen]; omega) (Nat.le_refl _) I₁) fun u J => fin u (hlen ▸ J)

end VG.Proof.Dsa.X86.KeyRandom
