module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesGcm.Arm.Env
meta import VerifiedGarbage.Proof.AesGcm.Arm.Env
public import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Copy
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Copy
meta import VerifiedGarbage.Spec.Gcm.OutOfPlace
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.Cmac.Spec

/-! ### `AesGcm.Arm.Gather.Loop`, which this module and modules that import it used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, ARMv7: gathering the slices

Untrusted: everything here is checked by Lean. `gather` copies the `cnt`
slices that the descriptors at `r0` list, one after the other, to `r2`
(`gather_wp`): with `i` of them copied (`GInv`), `r0` is at descriptor `i`,
`lr` holds `cnt - i`, `r2` is `gatheredLen` of the first `i` past `dst`, and
the memory is the one on entry with their concatenation (`gathered`) written
at `dst`. The descriptors and the slices are apart from `dst`, so they are
what they were on entry. Descriptor `i` is at `Src + 8i`: the slice's address
(`sb`), then its length (`sl`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.Gather

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_cmp0 dec32 z_dec covers_off covers_of_mem add_ofNat_zero)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

/-- What the gathering keeps: the other registers, the stack pointer and the
permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Keeps.gkeeps {s t : State} (h : Keeps s t) : GKeeps s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (by
    simp only [copyRegs, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with e | e | e | e <;> simp [e])), h.sp, h.rd, h.wr⟩

section
variable (m : Mem) (Src : BitVec 32)

/-- Slice `i`: its address and its length, from its descriptor at `Src + 8i`. -/
abbrev sb (i : Nat) : BitVec 32 := m.readW (State.addr (Src + BitVec.ofNat 32 (8 * i))) 32
abbrev sl (i : Nat) : Nat := (m.readW (State.addr (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4)) 32).toNat

end

/-- Descriptor `i`'s words, from the 32-bit pointer to the descriptors. -/
theorem descA {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) (d : Nat)
    (hd : d < 8) :
    State.addr Src + BitVec.ofNat 64 (i * (2 * (32 / 8))) + BitVec.ofNat 64 d =
      State.addr (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show i * (2 * (32 / 8)) + d = 8 * i + d by omega_using [], addr_add (by omega_using [hdw, hi, hd])]

theorem descA0 {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    State.addr Src + BitVec.ofNat 64 (i * (2 * (32 / 8))) = State.addr (Src + BitVec.ofNat 32 (8 * i)) := by
  have := descA hdw hi 0 (by decide)
  rwa [add_ofNat_zero, add_ofNat_zero] at this

theorem gl_succ {m : Mem} {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    gatheredLen 32 m (State.addr Src) (i + 1) = gatheredLen 32 m (State.addr Src) i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide)]

theorem pt_succ {m : Mem} {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    gathered 32 m (State.addr Src) (i + 1) =
      gathered 32 m (State.addr Src) i ++ bytesAt m (State.addr (sb m Src i)) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide), descA0 hdw hi]
  rfl

theorem gl_mono (m : Mem) (Src : BitVec 32) {cnt i j : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (h : i ≤ j)
    (hj : j ≤ cnt) : gatheredLen 32 m (State.addr Src) i ≤ gatheredLen 32 m (State.addr Src) j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ hdw (by omega_using [hj])]; exact Nat.le_trans (ih (by omega_using [h]) (by omega_using [hj])) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    (⟨State.addr (sb m Src i), sl m Src i⟩ : Region) ∈ Sig.listed 32 m .u8 (State.addr Src) cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  rw [show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide), descA0 hdw hi]
  simp only [Elem.size, Nat.mul_one]
  rfl

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : BitVec 32) (cnt L : Nat) : Prop where
  r0 : t.gpr .r0 = Src
  lr : t.gpr .lr = BitVec.ofNat 32 cnt
  r2 : t.gpr .r2 = Dst
  hcnt : cnt < 2 ^ 32
  dw : Src.toNat + cnt * 8 ≤ 2 ^ 32
  fitD : Dst.toNat + L ≤ 2 ^ 32
  len : gatheredLen 32 t.mem (State.addr Src) cnt = L
  dsr : Covers [⟨State.addr Src, cnt * 8⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 32 t.mem .u8 (State.addr Src) cnt, Covers [r] (t.rd ++ t.wr)
  lfit : ∀ r ∈ Sig.listed 32 t.mem .u8 (State.addr Src) cnt, r.base.toNat + r.len ≤ 2 ^ 32
  dw' : Covers [⟨State.addr Dst, L⟩] t.wr
  dsd : (⟨State.addr Src, cnt * 8⟩ : Region).Disjoint ⟨State.addr Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 32 t.mem .u8 (State.addr Src) cnt, r.Disjoint ⟨State.addr Dst, L⟩

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : BitVec 32) (cnt i : Nat) : Prop where
  r0 : u.gpr .r0 = Src + BitVec.ofNat 32 (8 * i)
  lr : u.gpr .lr = BitVec.ofNat 32 (cnt - i)
  r2 : u.gpr .r2 = Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)
  mem : u.mem = writeBytes t.mem (State.addr Dst) (gathered 32 t.mem (State.addr Src) i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.r0]; simp, by rw [h.lr, Nat.sub_zero], by rw [h.r2]; simp [gatheredLen, Sig.listed],
    by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩

theorem next_ok (u : State) {A₀ : BitVec 32} {w : Nat} (h0 : u.gpr .r0 = A₀) (hlr : u.gpr .lr = BitVec.ofNat 32 w) :
    ∃ u', runBlock isa next u = some u' ∧ u'.gpr .r0 = A₀ + BitVec.ofNat 32 8 ∧
      u'.gpr .lr = BitVec.ofNat 32 w - BitVec.ofNat 32 1 ∧ u'.z = (BitVec.ofNat 32 w - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .lr → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧
      u'.wr = u.wr := by
  refine ⟨(subFlags (u.setReg .r0 (A₀ + BitVec.ofNat 32 8)) (BitVec.ofNat 32 w) (BitVec.ofNat 32 1)).setReg .lr
      (BitVec.ofNat 32 w - BitVec.ofNat 32 1), by arun [next, h0, hlr], ?_, ?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl,
    rfl⟩
  · simp [gpr_setReg, h0]
  · simp [gpr_setReg, hlr]
  · simp [z_setReg, hlr]
  · simp [gpr_setReg, h₁, h₂]

section
variable {t u : State} {Src Dst : BitVec 32} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

theorem gl_le (hi : i ≤ cnt) : gatheredLen 32 t.mem (State.addr Src) i ≤ L :=
  h.len ▸ gl_mono t.mem Src h.dw hi (Nat.le_refl _)

/-- What the copy of slice `i` needs, with `i` copied. -/
theorem slicePre_of (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    SlicePre u (Src + BitVec.ofNat 32 (8 * i)) (sb t.mem Src i)
      (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)) (sl t.mem Src i) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (State.addr Src) (i + 1) ≤ L := gl_le h (by omega_using [hi])
  have hlen : (gathered 32 t.mem (State.addr Src) i).length = gatheredLen 32 t.mem (State.addr Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨State.addr Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega_using [hgl]
  -- The descriptor.
  have a0 : State.addr (Src + BitVec.ofNat 32 (8 * i)) = State.addr Src + BitVec.ofNat 64 (8 * i) :=
    addr_add (by omega_using [hi, hdw])
  have a4 : State.addr (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      State.addr Src + BitVec.ofNat 64 (8 * i + 4) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_add (by omega_using [hi, hdw])]
  have din (d : Nat) (hd : d + 4 ≤ cnt * 8) : InRegions (u.rd ++ u.wr) (State.addr Src + BitVec.ofNat 64 d) 4 := by
    rw [hu.keep.rd, hu.keep.wr]; exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega_using [hc, hd])⟩
  have dsub (d : Nat) (hd : d + 4 ≤ cnt * 8) :
      Region.Sub ⟨State.addr Src + BitVec.ofNat 64 d, 4⟩ ⟨State.addr Src, cnt * 8⟩ := Offset.sub_base _ hd
  have dkeep (d : Nat) (hd : d + 4 ≤ cnt * 8) :
      u.mem.readW (State.addr Src + BitVec.ofNat 64 d) 32 = t.mem.readW (State.addr Src + BitVec.ofNat 64 d) 32 :=
    hfr.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.dsd.sub_left (dsub d hd)) (by decide)
  -- The slice.
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨State.addr (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨State.addr Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  -- Where the slice goes: past the first `i`, unless it is empty (and may then be at the end of the
  -- address space, where `r2` wraps).
  have aD (hp : 0 < sl t.mem Src i) : State.addr (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)) =
      State.addr Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (State.addr Src) i) := addr_add (by omega_using [hfD, hgl, hp])
  have hsub : (⟨State.addr (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)), sl t.mem Src i⟩ :
      Region).Sub ⟨State.addr Dst, L⟩ := by
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp]; exact Offset.sub_base _ hgl
    · intro x hx; simp only [Region.Contains] at hx; omega
  exact
    { r0 := hu.r0
      r2 := hu.r2
      d0 := by rw [a0]; exact din _ (by omega_using [hi])
      d4 := by rw [a4]; exact din _ (by omega_using [hi])
      w0 := by rw [a0, dkeep _ (by omega_using [hi]), ← a0]
      w4 := by rw [a4, dkeep _ (by omega_using [hi]), ← a4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      lt := by simp only [sl]; exact BitVec.isLt _
      fitS := by simpa [addr_toNat] using hfit
      fitD := by
        by_cases hp : 0 < sl t.mem Src i
        · rw [toNat_add_of_lt (by omega_using [hfD, hgl, hp])]; omega_using [hfD, hgl]
        · have := (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)).isLt; omega_using [hp]
      rd := by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem
      wr := fun hp => by
        rw [hu.keep.wr, aD hp]
        exact covers_off h.dw' hgl (by omega_using [hfD])
      disj := hsd.sub_right hsub
      dd := by
        rw [a4]
        exact (h.dsd.sub_left (dsub _ (by omega_using [hi]))).sub_right hsub }

/-- One iteration: slice `i` copied, `r0` at the next descriptor and `lr`
decremented. -/
theorem body_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.seq copySlice (.block next)) u fun u' => GInv t u' Src Dst cnt (i + 1) ∧
      u'.z = decide (i + 1 = cnt) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (State.addr Src) (i + 1) ≤ L := gl_le h (by omega_using [hi])
  have hlen : (gathered 32 t.mem (State.addr Src) i).length = gatheredLen 32 t.mem (State.addr Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨State.addr Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega_using [hgl]
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨State.addr (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨State.addr Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  have aD (hp : 0 < sl t.mem Src i) : State.addr (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)) =
      State.addr Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (State.addr Src) i) := addr_add (by omega_using [hfD, hgl, hp])
  have hsp := slicePre_of h hi hu
  refine WP.seq (WP.mono (copySlice_wp u hsp) fun u₂ ⟨m₂, r2₂, kp₂⟩ => ?_)
  obtain ⟨u₃, run₃, r0₃, lr₃, z₃, g₃, m₃, sp₃, rd₃, wr₃⟩ :=
    next_ok u₂ (w := cnt - i) (by rw [kp₂.gpr _ (by decide), hu.r0]) (by rw [kp₂.gpr _ (by decide), hu.lr])
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (State.addr (sb t.mem Src i)) (sl t.mem Src i) =
      bytesAt t.mem (State.addr (sb t.mem Src i)) (sl t.mem Src i) := by
    refine Proof.AesGcm.Arm.bytesAt_frame hfr (fun r hr => ?_) (by omega_using [hfD, hgl])
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨⟨?_, ?_, ?_, ?_, hu.keep.trans (kp₂.gkeeps.trans
    ⟨fun r hr => g₃ r (by intro e; subst e; simp [gatherRegs] at hr) (by intro e; subst e; simp [gatherRegs] at hr),
      sp₃, rd₃, wr₃⟩)⟩, ?_⟩
  · rw [r0₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  · rw [lr₃, dec32 hi hc]
  · rw [g₃ _ (by decide) (by decide), r2₂, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← gl_succ hdw hi]
  · rw [m₃, m₂, hbytes, hu.mem, pt_succ hdw hi]
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp, ← hlen, writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega_using [hfD, hgl])]
    · have h0 : sl t.mem Src i = 0 := by omega_using [hp]
      rw [h0]; simp [bytesAt, writeBytes_nil]
  · rw [z₃, dec32 hi hc, z_dec hi hc]

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (t : State) {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' =>
      t'.mem = writeBytes t.mem (State.addr Dst) (gathered 32 t.mem (State.addr Src) cnt) ∧ GKeeps t t' := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.mono (body_wp h hi hu) fun u₃ ⟨h₃, z₃⟩ => ?_
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = cnt) := eval_ne' z₃
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], h₃⟩

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (t : State) {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' =>
      t'.mem = writeBytes t.mem (State.addr Dst) (gathered 32 t.mem (State.addr Src) cnt) ∧ GKeeps t t' := by
  obtain ⟨t₁, run₁, ht₁⟩ : ∃ t₁, runBlock isa [.cmp .lr (imm 0)] t = some t₁ ∧
      t₁ = subFlags t (t.gpr .lr) (BitVec.ofNat 32 0) := ⟨_, by arun [], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  subst ht₁
  have hz : (subFlags t (t.gpr .lr) (BitVec.ofNat 32 0)).z = decide (cnt = 0) := by
    rw [Proof.AesGcm.Arm.z_subFlags, h.lr]; exact z_ne0 h.hcnt
  refine WP.ite (decide (cnt = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [gathered, Sig.listed, writeBytes_nil], ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩ := h
    have h' : GatherPre (subFlags t (t.gpr .lr) (BitVec.ofNat 32 0)) Src Dst cnt L :=
      ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩
    exact WP.mono (gatherLoop_wp _ h' (by omega_using [h0])) fun t' ⟨m, k⟩ => ⟨m, ⟨k.gpr, k.sp, k.rd, k.wr⟩⟩

/-! ## Blocks -/

theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

/-- A block run as two. -/
theorem WP.split {l₁ l₂ : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block (l₁ ++ l₂)) s Q) :
    WP isa (.seq (.block l₁) (.block l₂)) s Q :=
  WP.seq (WP.block_append_iff.mp h)

end VG.Proof.AesGcm.Arm.Gather

end

end

/-!
# Gathering a list of slices, ARMv7: constant time

Untrusted: everything here is checked by Lean. Runs are related piece by
piece from given states (`Eq2`), as AES-OCB's are (`Proof.AesOcb.Arm`): a
frame's words are read and written through `r12`, which `setFp` sets to the
stack pointer, the same in both runs (`rel_fp`). Two runs of `gather` whose
descriptors agree, from states the correctness proof describes with the same
arguments (`GatherPre`), leak the same trace (`gather_rel`): the gathering
loads the descriptors from where they are, and copies each slice from and to
the addresses they give, with branches on the number of slices and their
lengths (`copySlice_rel`, by the taint analysis from the registers the
correctness proof pins to the same values in both runs).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.Gather

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.SealGather
open VG.Spec.Gcm (gathered gatheredLen)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' add_ofNat_zero)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact Taint.agree_ofRegs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT :=
  rel_taint [] (by simp) ⟨.block [], rfl⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- A frame that reserves stack, around a body whose runs leak the same. -/
theorem rel_alloc {n : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hb : RelCT isa (Eq2 (allocated n σ₁) (allocated n σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.alloc n) body (.free n)) TT := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rfl, rfl⟩ := hp
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      have ea := alloc_eq p₁
      have eb := alloc_eq p₂
      subst ea eb
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨rfl, rfl⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      rfl

/-- `setFp`: `r12` at the stack pointer. -/
theorem setFp_wp (σ : State) : WP isa (.block setFp) σ fun τ => τ.gpr .r12 = σ.sp := by
  refine WP.run ⟨_, by arun [setFp], rfl⟩ fun τ hτ => ?_
  subst hτ
  simp [gpr_setReg, add_ofNat_zero]

/-- A block of the frame's words, reached through `r12` at the stack pointer,
the same in both runs. -/
theorem rel_fp {l : List Instr} {σ₁ σ₂ : State} (hsp : σ₁.sp = σ₂.sp)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r12]) (.block l) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block setFp) (.block l)) TT :=
  rel_seq (rel_taint [] (by simp) ⟨_, by taint_decide⟩) (setFp_wp σ₁) (setFp_wp σ₂) fun _ _ h₁ h₂ =>
    rel_taint [.r12] (by simp [h₁, h₂, hsp]) hc

/-! ## Copying a slice -/

/-- `copySlice` in two runs copying the same slice: the branches are on its
length, the addresses are its and the descriptor's. -/
theorem copySlice_rel {σ₁ σ₂ : State} {A₀ S D : BitVec 32} {n : Nat} (h₁ : SlicePre σ₁ A₀ S D n)
    (h₂ : SlicePre σ₂ A₀ S D n) : RelCT isa (Eq2 σ₁ σ₂) copySlice TT := by
  have tw : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r1, .r2, .r3]) copyWords h).isSome = true :=
    ⟨_, by taint_decide⟩
  have tl : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r1, .r2, .r3]) copyLoop h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.r0, .r2] (by simp [h₁.r0, h₂.r0, h₁.r2, h₂.r2]) ⟨_, by taint_decide⟩)
    (wordsArg_wp h₁) (wordsArg_wp h₂) fun τ₁ τ₂ w₁ w₂ => ?_
  refine rel_seq (rel_ite (eval_eq' w₁.z) (eval_eq' w₂.z) (fun _ => rel_skip) fun _ =>
      rel_taint [.r1, .r2, .r3] (by simp [w₁.r1, w₂.r1, w₁.r2, w₂.r2, w₁.r3, w₂.r3]) tw)
    (words_wp h₁ w₁) (words_wp h₂ w₂) fun v₁ v₂ x₁ x₂ => ?_
  refine rel_seq (rel_taint [.r0, .r1, .r2] (by simp [x₁.r0, x₂.r0, x₁.r1, x₂.r1, x₁.r2, x₂.r2])
      ⟨_, by taint_decide⟩) (bytesArg_wp h₁ x₁) (bytesArg_wp h₂ x₂) fun b₁ b₂ y₁ y₂ => ?_
  exact rel_ite (eval_eq' y₁.z) (eval_eq' y₂.z) (fun _ => rel_skip) fun _ =>
    rel_taint [.r1, .r2, .r3] (by simp [y₁.r1, y₂.r1, y₁.r2, y₂.r2, y₁.r3, y₂.r3]) tl

/-! ## Gathering -/

/-- The descriptors agree in two memories: so do the slices they list. -/
theorem desc_agree {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
    (hd : ∀ j < cnt * 8, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j)) {i : Nat} (hi : i ≤ cnt) :
    ∀ a, (Sig.descRegion 32 Src i).Contains a 1 → m₁ a = m₂ a := by
  intro a ha
  simp only [Sig.descRegion, Region.Contains] at ha
  have e : Src + BitVec.ofNat 64 (a - Src).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← e]
  exact hd _ (by have := Nat.mul_le_mul_right 8 hi; simp only [show 2 * (32 / 8) = 8 from rfl] at ha; omega_using [hi, ha])

section
variable {m₁ m₂ : Mem} {Src : BitVec 32} {cnt : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32)
  (hd : ∀ j < cnt * 8, m₁ (State.addr Src + BitVec.ofNat 64 j) = m₂ (State.addr Src + BitVec.ofNat 64 j))
include hd

omit hdw in
theorem gl_agree {i : Nat} (hi : i ≤ cnt) :
    gatheredLen 32 m₁ (State.addr Src) i = gatheredLen 32 m₂ (State.addr Src) i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 32 .u8 (State.addr Src) i (desc_agree hd hi)]

omit hdw in
theorem desc_word {d : Nat} (h : d + 4 ≤ cnt * 8) :
    m₁.readW (State.addr Src + BitVec.ofNat 64 d) 32 = m₂.readW (State.addr Src + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega_using [h, hk])

include hdw

theorem sb_agree {i : Nat} (hi : i < cnt) : sb m₁ Src i = sb m₂ Src i := by
  simp only [sb]
  rw [← descA0 hdw hi]
  exact desc_word hd (by omega_using [hi])

theorem sl_agree {i : Nat} (hi : i < cnt) : sl m₁ Src i = sl m₂ Src i := by
  simp only [sl]
  rw [← descA hdw hi 4 (by decide), Offset.add_ofNat_add_ofNat, desc_word hd (by omega_using [hi])]

end

/-- `GatherPre` after `cmp`, which changes only the flags. -/
theorem GatherPre.cmp {t : State} {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GatherPre (subFlags t (t.gpr .lr) (BitVec.ofNat 32 0)) Src Dst cnt L := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩ := h
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩

section
variable {t₁ t₂ : State} {Src Dst : BitVec 32} {cnt L : Nat}
  (hd : ∀ j < cnt * 8, t₁.mem (State.addr Src + BitVec.ofNat 64 j) = t₂.mem (State.addr Src + BitVec.ofNat 64 j))
  (h₁ : GatherPre t₁ Src Dst cnt L) (h₂ : GatherPre t₂ Src Dst cnt L)
include hd h₁ h₂

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i) (.seq copySlice (.block next))
      (fun u₁ u₂ => (GInv t₁ u₁ Src Dst cnt (i + 1) ∧ u₁.z = decide (i + 1 = cnt)) ∧
        (GInv t₂ u₂ Src Dst cnt (i + 1) ∧ u₂.z = decide (i + 1 = cnt))) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq copySlice (.block next)) TT := by
    intro σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨g₁, g₂⟩ e₁ e₂
    have p₁ := slicePre_of h₁ hi g₁
    have p₂ := slicePre_of h₂ hi g₂
    rw [← sb_agree h₁.dw hd hi, ← sl_agree h₁.dw hd hi, ← gl_agree hd (Nat.le_of_lt hi)] at p₂
    refine rel_seq (copySlice_rel p₁ p₂) (copySlice_wp σ₁ p₁) (copySlice_wp σ₂ p₂) (fun τ₁ τ₂ c₁ c₂ => ?_)
      σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨rfl, rfl⟩ e₁ e₂
    refine rel_taint [.r0, .lr] ?_ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by rw [c₁.2.2.gpr _ (by decide), c₂.2.2.gpr _ (by decide), g₁.r0, g₂.r0],
      by rw [c₁.2.2.gpr _ (by decide), c₂.2.2.gpr _ (by decide), g₁.lr, g₂.lr]⟩
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ => ⟨body_wp h₁ hi g₁, body_wp h₂ hi g₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `gatherLoop`, in two runs. -/
theorem gatherLoop_rel (hpos : cnt ≠ 0) : RelCT isa (Eq2 t₁ t₂) gatherLoop TT := by
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega_using [hpos], GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel hd h₁ h₂ hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩
    have ev₁ := eval_ne' z₁
    have ev₂ := eval_ne' z₂
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega_using [hi, ht]
    exact ⟨cnt - (i + 1), by omega_using [hi], i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

end

/-- `gather`, in two runs. -/
theorem gather_rel {e₁ e₂ : State} {Src Dst : BitVec 32} {cnt L : Nat}
    (hd : ∀ j < cnt * 8, e₁.mem (State.addr Src + BitVec.ofNat 64 j) = e₂.mem (State.addr Src + BitVec.ofNat 64 j))
    (h₁ : GatherPre e₁ Src Dst cnt L) (h₂ : GatherPre e₂ Src Dst cnt L) : RelCT isa (Eq2 e₁ e₂) gather TT := by
  have cmp_wp (e : State) : WP isa (.block [.cmp .lr (imm 0)]) e fun t => t = subFlags e (e.gpr .lr) (BitVec.ofNat 32 0) :=
    WP.run ⟨_, by arun [], rfl⟩ fun _ h => h.symm
  refine rel_seq (rel_taint [.lr] (by simp [h₁.lr, h₂.lr]) ⟨_, by taint_decide⟩) (cmp_wp e₁) (cmp_wp e₂)
    fun t₁ t₂ ht₁ ht₂ => ?_
  subst ht₁ ht₂
  have hz (e : State) (h : GatherPre e Src Dst cnt L) :
      (subFlags e (e.gpr .lr) (BitVec.ofNat 32 0)).z = decide (cnt = 0) := by
    rw [Proof.AesGcm.Arm.z_subFlags, h.lr]; exact z_ne0 h.hcnt
  refine rel_ite (eval_eq' (hz e₁ h₁)) (eval_eq' (hz e₂ h₂)) (fun _ => rel_skip) fun hf => ?_
  exact gatherLoop_rel hd h₁.cmp h₂.cmp (by simpa using hf)

end VG.Proof.AesGcm.Arm.Gather
