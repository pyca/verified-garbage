module

public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
public import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-! # The cached digest copied into the frame (x86)

`copyExpanded` loads the second argument, the address of a seed's SHA-512 digest, into
ECX, and copies its 16 words to frame offset 192, where the seed's hash leaves the
digest; it writes only EAX, ECX and those 64 bytes. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

/-- Byte `i` of a little-endian 32-bit word. -/
theorem readW_byte32 (m : Mem) (a : Addr) {i : Nat} (hi : i < 4) :
    m (a + BitVec.ofNat 64 i) = (m.readW a 32).extractLsb' (8 * i) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 4) hi]
  simp only [Mem.readW]
  rfl

/-- 64 bytes from their sixteen little-endian 32-bit words. -/
theorem bytesAt_of_words32 {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 16, m'.readW (p' + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    Spec.Sha512.bytesAt m' p' 64 = Spec.Ed25519.bytesAt m p 64 := by
  simp only [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ∀ q : Addr, q + BitVec.ofNat 64 i = q + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) := by
    intro q
    have e : BitVec.ofNat 64 i = BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1; omega
    rw [e, BitVec.add_assoc]
  have hk : i / 4 < 16 := by omega
  have hj : i % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [ha p', ha p, readW_byte32 m' _ hj, readW_byte32 m _ hj, h _ hk]

variable {E : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {R W : List Region}

/-- `copyPtr` loads the second argument into ECX. -/
theorem copyPtr_ok {t : State} (hc : Ctx E g m₀ R W t)
    (hr : InRegions (t.rd ++ t.wr) (addr E 264) 4) :
    WP isa (.block copyPtr) t fun u => Ctx E g m₀ R W u ∧ u.mem = t.mem ∧
      u.gpr .ecx = t.mem.readW (addr E 264) 32 := by
  show WP isa (.block [.mov .ecx (.mem ⟨.esp, 264⟩)]) t _
  refine Wp.wp_ldm hc.esp hr fun u hu => WP.block_nil ⟨?_, hu.mem, hu.gpr⟩
  refine hc.regs hu.rd hu.wr (hu.other _ (by decide)) (fun r hr _ => hu.other r ?_) hu.mem
  rintro rfl
  simp [calleeSaved] at hr

/-- What the copy of the first `k` words keeps and establishes. -/
structure CopyInv (E p : BitVec 32) (t : State) (k : Nat) (u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  regs : ∀ r, r ≠ .eax → u.gpr r = t.gpr r
  frame : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 192, 64⟩] t.mem u.mem
  words : ∀ j < k, u.mem.readW (addr E (192 + 4 * j)) 32 = t.mem.readW (addr p (4 * j)) 32

theorem copyWords_prefix {t : State} {p : BitVec 32} (he : t.gpr .esp = E) (hp : t.gpr .ecx = p)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ t.wr)
    (hpf : p.toNat + 64 ≤ 2 ^ 32) (hsrc : (⟨p.setWidth 64, 64⟩ : Region) ∈ t.rd ++ t.wr)
    (hd : Region.Disjoint ⟨p.setWidth 64, 64⟩ ⟨E.setWidth 64 + BitVec.ofNat 64 192, 64⟩) :
    ∀ k ≤ 16, WP isa (.block ((List.range k).flatMap copyDigestWord)) t (CopyInv E p t k)
  | 0, _ => WP.block_nil ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyWords_prefix he hp hf hw hpf hsrc hd k (by omega)) fun u hu => ?_
    have ue : u.gpr .esp = E := (hu.regs _ (by decide)).trans he
    have up : u.gpr .ecx = p := (hu.regs _ (by decide)).trans hp
    have ap : addr p (4 * k) = p.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)
    have aE : addr E (192 + 4 * k) = E.setWidth 64 + BitVec.ofNat 64 (192 + 4 * k) := addr_eq (by omega)
    have ur : InRegions (u.rd ++ u.wr) (addr p (4 * k)) 4 := by
      refine ⟨_, by rw [hu.rd, hu.wr]; exact hsrc, ?_⟩
      rw [ap]
      exact Offset.contains_base _ (by omega) (by omega)
    have uw : InRegions u.wr (addr E (192 + 4 * k)) 4 := by
      refine ⟨_, by rw [hu.wr]; exact hw, ?_⟩
      rw [aE]
      exact Offset.contains_base _ (by omega) (by omega)
    have same : u.mem.readW (addr p (4 * k)) 32 = t.mem.readW (addr p (4 * k)) 32 := by
      rw [ap]
      refine hu.frame.readW (r := ⟨p.setWidth 64, 64⟩) (Offset.contains_base _ (by omega) (by omega)) ?_
        (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact hd
    simp only [copyDigestWord, at_]
    refine Wp.wp_ldm up ur fun v hv => ?_
    refine Wp.wp_stm ((hv.other _ (by decide)).trans ue) (hv.wr ▸ uw) fun w hw' => WP.block_nil ?_
    have mw : w.mem = u.mem.writeW (addr E (192 + 4 * k)) (t.mem.readW (addr p (4 * k)) 32) := by
      rw [hw'.mem, hv.mem, hv.gpr, same]
    refine ⟨hw'.rd.trans (hv.rd.trans hu.rd), hw'.wr.trans (hv.wr.trans hu.wr),
      fun r h => by rw [hw'.gpr, hv.other r h, hu.regs r h], ?_, fun j hj => ?_⟩
    · rw [mw, aE]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by decide))
    · rw [mw]
      by_cases hjk : j = k
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := addr E (192 + 4 * j)) (b := addr E (192 + 4 * k)) ?_ (by decide)]
        · exact hu.words j (by omega)
        · rw [aE, addr_eq (by omega)]
          exact Offset.sep _ (by omega) (by omega) (by omega)

/-- `copyDigestWords` copies the 64 bytes at ECX to frame offset 192. -/
theorem copyWords_ok {t : State} (hc : Ctx E g m₀ R W t) (hf : E.toNat + 256 ≤ 2 ^ 32)
    {p : BitVec 32} (hp : t.gpr .ecx = p) (hpf : p.toNat + 64 ≤ 2 ^ 32)
    (hsrc : (⟨p.setWidth 64, 64⟩ : Region) ∈ t.rd ++ t.wr)
    (hd : Region.Disjoint ⟨p.setWidth 64, 64⟩ ⟨E.setWidth 64 + BitVec.ofNat 64 192, 64⟩) :
    WP isa (.block copyDigestWords) t fun u => Ctx E g m₀ R W u ∧
      Spec.Sha512.bytesAt u.mem (E.setWidth 64 + 192) 64 = Spec.Ed25519.bytesAt t.mem (p.setWidth 64) 64 := by
  have hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ t.wr := by rw [hc.wr]; exact List.mem_cons_self
  refine WP.mono (copyWords_prefix hc.esp hp hf hw hpf hsrc hd 16 (Nat.le_refl _)) fun u hu => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr (hu.regs _ (by decide)) (fun r hr _ => hu.regs r ?_) hu.frame ?_
    · rintro rfl
      simp [calleeSaved] at hr
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by decide))
  · refine bytesAt_of_words32 fun k hk => ?_
    have h := hu.words k hk
    rw [addr_eq (by omega), addr_eq (by omega), BitVec.ofNat_add] at h
    rw [BitVec.add_assoc]
    exact h

/-- `copyExpanded` copies the 64 bytes at the second argument to frame offset 192. -/
theorem copyExpanded_ok {t : State} (hc : Ctx E g m₀ R W t) (hf : E.toNat + 256 ≤ 2 ^ 32)
    (harg : InRegions (t.rd ++ t.wr) (addr E 264) 4) {p : BitVec 32}
    (hp : t.mem.readW (addr E 264) 32 = p) (hpf : p.toNat + 64 ≤ 2 ^ 32)
    (hsrc : (⟨p.setWidth 64, 64⟩ : Region) ∈ t.rd ++ t.wr)
    (hd : Region.Disjoint ⟨p.setWidth 64, 64⟩ ⟨E.setWidth 64 + BitVec.ofNat 64 192, 64⟩) :
    WP isa copyExpanded t fun u => Ctx E g m₀ R W u ∧
      Spec.Sha512.bytesAt u.mem (E.setWidth 64 + 192) 64 = Spec.Ed25519.bytesAt t.mem (p.setWidth 64) 64 := by
  refine WP.seq (WP.mono (copyPtr_ok hc harg) fun u ⟨hu, hm, he⟩ => ?_)
  have hsrc' : (⟨p.setWidth 64, 64⟩ : Region) ∈ u.rd ++ u.wr := by
    rw [hu.rd, hu.wr]; rw [hc.rd, hc.wr] at hsrc; exact hsrc
  refine WP.mono (copyWords_ok hu hf (he.trans hp) hpf hsrc' hd) fun v ⟨hv, hb⟩ => ⟨hv, ?_⟩
  rw [hb, hm]

end VG.Proof.Ed25519.X86.Whole
