import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Copy
import VerifiedGarbage.Proof.Gcm.SealGather

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
    show i * (2 * (32 / 8)) + d = 8 * i + d by omega, addr_add (by omega)]

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
    · rw [gl_succ hdw (by omega)]; exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_add_right _ _)

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
  have hgl : gatheredLen 32 t.mem (State.addr Src) (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 32 t.mem (State.addr Src) i).length = gatheredLen 32 t.mem (State.addr Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨State.addr Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega
  -- The descriptor.
  have a0 : State.addr (Src + BitVec.ofNat 32 (8 * i)) = State.addr Src + BitVec.ofNat 64 (8 * i) :=
    addr_add (by omega)
  have a4 : State.addr (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      State.addr Src + BitVec.ofNat 64 (8 * i + 4) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, addr_add (by omega)]
  have din (d : Nat) (hd : d + 4 ≤ cnt * 8) : InRegions (u.rd ++ u.wr) (State.addr Src + BitVec.ofNat 64 d) 4 := by
    rw [hu.keep.rd, hu.keep.wr]; exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
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
      State.addr Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (State.addr Src) i) := addr_add (by omega)
  have hsub : (⟨State.addr (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)), sl t.mem Src i⟩ :
      Region).Sub ⟨State.addr Dst, L⟩ := by
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp]; exact Offset.sub_base _ hgl
    · intro x hx; simp only [Region.Contains] at hx; omega
  exact
    { r0 := hu.r0
      r2 := hu.r2
      d0 := by rw [a0]; exact din _ (by omega)
      d4 := by rw [a4]; exact din _ (by omega)
      w0 := by rw [a0, dkeep _ (by omega), ← a0]
      w4 := by rw [a4, dkeep _ (by omega), ← a4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      lt := by simp only [sl]; exact BitVec.isLt _
      fitS := by simpa [addr_toNat] using hfit
      fitD := by
        by_cases hp : 0 < sl t.mem Src i
        · rw [toNat_add_of_lt (by omega)]; omega
        · have := (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)).isLt; omega
      rd := by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem
      wr := fun hp => by
        rw [hu.keep.wr, aD hp]
        exact covers_off h.dw' hgl (by omega)
      disj := hsd.sub_right hsub
      dd := by
        rw [a4]
        exact (h.dsd.sub_left (dsub _ (by omega))).sub_right hsub }

/-- One iteration: slice `i` copied, `r0` at the next descriptor and `lr`
decremented. -/
theorem body_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.seq copySlice (.block next)) u fun u' => GInv t u' Src Dst cnt (i + 1) ∧
      u'.z = decide (i + 1 = cnt) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (State.addr Src) (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 32 t.mem (State.addr Src) i).length = gatheredLen 32 t.mem (State.addr Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨State.addr Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨State.addr (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨State.addr Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  have aD (hp : 0 < sl t.mem Src i) : State.addr (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (State.addr Src) i)) =
      State.addr Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (State.addr Src) i) := addr_add (by omega)
  have hsp := slicePre_of h hi hu
  refine WP.seq (WP.mono (copySlice_wp u hsp) fun u₂ ⟨m₂, r2₂, kp₂⟩ => ?_)
  obtain ⟨u₃, run₃, r0₃, lr₃, z₃, g₃, m₃, sp₃, rd₃, wr₃⟩ :=
    next_ok u₂ (w := cnt - i) (by rw [kp₂.gpr _ (by decide), hu.r0]) (by rw [kp₂.gpr _ (by decide), hu.lr])
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (State.addr (sb t.mem Src i)) (sl t.mem Src i) =
      bytesAt t.mem (State.addr (sb t.mem Src i)) (sl t.mem Src i) := by
    refine Proof.AesGcm.Arm.bytesAt_frame hfr (fun r hr => ?_) (by omega)
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
    · rw [aD hp, ← hlen, writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)]
    · have h0 : sl t.mem Src i = 0 := by omega
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
    exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

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
    exact WP.mono (gatherLoop_wp _ h' (by omega)) fun t' ⟨m, k⟩ => ⟨m, ⟨k.gpr, k.sp, k.rd, k.wr⟩⟩

/-! ## Blocks -/

theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

/-- A block run as two. -/
theorem WP.split {l₁ l₂ : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block (l₁ ++ l₂)) s Q) :
    WP isa (.seq (.block l₁) (.block l₂)) s Q :=
  WP.seq (WP.block_append_iff.mp h)

end VG.Proof.AesGcm.Arm.Gather
