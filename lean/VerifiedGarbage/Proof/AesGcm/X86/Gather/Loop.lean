import VerifiedGarbage.Proof.AesGcm.X86.Gather.Copy
import VerifiedGarbage.Proof.Gcm.SealGather

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: gathering the slices

Untrusted: everything here is checked by Lean. `gather` copies the `cnt`
slices that the descriptors at `esi` list, one after the other, to `edx`
(`gather_wp`): with `i` of them copied (`GInv`), `esi` is at descriptor `i`,
`ebx` holds `cnt - i`, `edx` is `gatheredLen` of the first `i` past `dst`, and
the memory is the one on entry with their concatenation (`gathered`) written
at `dst`. The descriptors and the slices are apart from `dst`, so they are
what they were on entry. Descriptor `i` is at `Src + 8i`: the slice's address
(`sb`), then its length (`sl`). A function gathering the slices runs in a
frame of stack of its own (`WP.alloc`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi]

/-- What the gathering keeps: the other registers and the permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Keeps.gkeeps {s t : State} (h : Keeps s t) : GKeeps s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (by
    simp only [copyRegs, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with e | e | e | e <;> simp [e])), h.rd, h.wr⟩

theorem add_ofNat_zero {w : Nat} (x : BitVec w) : x + BitVec.ofNat w 0 = x := BitVec.add_zero x

section
variable (m : Mem) (Src : BitVec 32)

/-- Slice `i`: its address and its length, from its descriptor at `Src + 8i`. -/
abbrev sb (i : Nat) : BitVec 32 := m.readW (w64 (Src + BitVec.ofNat 32 (8 * i))) 32
abbrev sl (i : Nat) : Nat := (m.readW (w64 (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4)) 32).toNat

end

/-- Descriptor `i`'s words, from the 32-bit pointer to the descriptors. -/
theorem descA {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) (d : Nat)
    (hd : d < 8) :
    w64 Src + BitVec.ofNat 64 (i * (2 * (32 / 8))) + BitVec.ofNat 64 d =
      w64 (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show i * (2 * (32 / 8)) + d = 8 * i + d by omega, w64_add (by omega)]

theorem descA0 {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    w64 Src + BitVec.ofNat 64 (i * (2 * (32 / 8))) = w64 (Src + BitVec.ofNat 32 (8 * i)) := by
  have := descA hdw hi 0 (by decide)
  rwa [add_ofNat_zero, add_ofNat_zero] at this

theorem gl_succ {m : Mem} {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    gatheredLen 32 m (w64 Src) (i + 1) = gatheredLen 32 m (w64 Src) i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide)]

theorem pt_succ {m : Mem} {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    gathered 32 m (w64 Src) (i + 1) =
      gathered 32 m (w64 Src) i ++ bytesAt m (w64 (sb m Src i)) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide), descA0 hdw hi]

theorem gl_mono (m : Mem) (Src : BitVec 32) {cnt i j : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (h : i ≤ j)
    (hj : j ≤ cnt) : gatheredLen 32 m (w64 Src) i ≤ gatheredLen 32 m (w64 Src) j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ hdw (by omega)]; exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    (⟨w64 (sb m Src i), sl m Src i⟩ : Region) ∈ Sig.listed 32 m .u8 (w64 Src) cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  rw [show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide), descA0 hdw hi]
  simp only [Elem.size, Nat.mul_one]

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : BitVec 32) (cnt L : Nat) : Prop where
  esi : t.gpr .esi = Src
  ebx : t.gpr .ebx = BitVec.ofNat 32 cnt
  edx : t.gpr .edx = Dst
  hcnt : cnt < 2 ^ 32
  dw : Src.toNat + cnt * 8 ≤ 2 ^ 32
  fitD : Dst.toNat + L ≤ 2 ^ 32
  len : gatheredLen 32 t.mem (w64 Src) cnt = L
  dsr : Covers [⟨w64 Src, cnt * 8⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 32 t.mem .u8 (w64 Src) cnt, Covers [r] (t.rd ++ t.wr)
  lfit : ∀ r ∈ Sig.listed 32 t.mem .u8 (w64 Src) cnt, r.base.toNat + r.len ≤ 2 ^ 32
  dw' : Covers [⟨w64 Dst, L⟩] t.wr
  dsd : (⟨w64 Src, cnt * 8⟩ : Region).Disjoint ⟨w64 Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 32 t.mem .u8 (w64 Src) cnt, r.Disjoint ⟨w64 Dst, L⟩

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : BitVec 32) (cnt i : Nat) : Prop where
  esi : u.gpr .esi = Src + BitVec.ofNat 32 (8 * i)
  ebx : u.gpr .ebx = BitVec.ofNat 32 (cnt - i)
  edx : u.gpr .edx = Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)
  mem : u.mem = writeBytes t.mem (w64 Dst) (gathered 32 t.mem (w64 Src) i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.esi]; simp, by rw [h.ebx, Nat.sub_zero], by rw [h.edx]; simp [gatheredLen, Sig.listed],
    by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩

theorem next_ok (u : State) {A₀ : BitVec 32} {w : Nat} (h0 : u.gpr .esi = A₀) (hlr : u.gpr .ebx = BitVec.ofNat 32 w) :
    ∃ u', runBlock isa next u = some u' ∧ u'.gpr .esi = A₀ + BitVec.ofNat 32 8 ∧
      u'.gpr .ebx = BitVec.ofNat 32 w - BitVec.ofNat 32 1 ∧ u'.zf = some (BitVec.ofNat 32 w - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .esi → r ≠ .ebx → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by xrun [next, h0, hlr], ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h0]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, hlr]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hlr]
  · simp [gpr_setReg, gpr_arithFlags, h₁, h₂]
  all_goals rfl

section
variable {t u : State} {Src Dst : BitVec 32} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

theorem gl_le (hi : i ≤ cnt) : gatheredLen 32 t.mem (w64 Src) i ≤ L :=
  h.len ▸ gl_mono t.mem Src h.dw hi (Nat.le_refl _)

/-- What the copy of slice `i` needs, with `i` copied. -/
theorem slicePre_of (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    SlicePre u (Src + BitVec.ofNat 32 (8 * i)) (sb t.mem Src i)
      (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)) (sl t.mem Src i) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (w64 Src) (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 32 t.mem (w64 Src) i).length = gatheredLen 32 t.mem (w64 Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨w64 Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega
  -- The descriptor.
  have a0 : w64 (Src + BitVec.ofNat 32 (8 * i)) = w64 Src + BitVec.ofNat 64 (8 * i) :=
    w64_add (by omega)
  have a4 : w64 (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      w64 Src + BitVec.ofNat 64 (8 * i + 4) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, w64_add (by omega)]
  have din (d : Nat) (hd : d + 4 ≤ cnt * 8) : InRegions (u.rd ++ u.wr) (w64 Src + BitVec.ofNat 64 d) 4 := by
    rw [hu.keep.rd, hu.keep.wr]; exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  have dsub (d : Nat) (hd : d + 4 ≤ cnt * 8) :
      Region.Sub ⟨w64 Src + BitVec.ofNat 64 d, 4⟩ ⟨w64 Src, cnt * 8⟩ := Offset.sub_base _ hd
  have dkeep (d : Nat) (hd : d + 4 ≤ cnt * 8) :
      u.mem.readW (w64 Src + BitVec.ofNat 64 d) 32 = t.mem.readW (w64 Src + BitVec.ofNat 64 d) 32 :=
    hfr.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.dsd.sub_left (dsub d hd)) (by decide)
  -- The slice.
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨w64 (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨w64 Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  -- Where the slice goes: past the first `i`, unless it is empty (and may then be at the end of the
  -- address space, where `r2` wraps).
  have aD (hp : 0 < sl t.mem Src i) : w64 (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)) =
      w64 Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (w64 Src) i) := w64_add (by omega)
  have hsub : (⟨w64 (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)), sl t.mem Src i⟩ :
      Region).Sub ⟨w64 Dst, L⟩ := by
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp]; exact Offset.sub_base _ hgl
    · intro x hx; simp only [Region.Contains] at hx; omega
  exact
    { esi := hu.esi
      edx := hu.edx
      d0 := by rw [a0]; exact din _ (by omega)
      d4 := by rw [a4]; exact din _ (by omega)
      w0 := by rw [a0, dkeep _ (by omega), ← a0]
      w4 := by rw [a4, dkeep _ (by omega), ← a4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      lt := by simp only [sl]; exact BitVec.isLt _
      fitS := by have := hfit; simp only at this; rwa [toNat_w64] at this
      fitD := by
        by_cases hp : 0 < sl t.mem Src i
        · rw [toNat_add_of_lt (by omega)]; omega
        · have := (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)).isLt; omega
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
      u'.zf = some (decide (i + 1 = cnt)) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (w64 Src) (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 32 t.mem (w64 Src) i).length = gatheredLen 32 t.mem (w64 Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨w64 Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨w64 (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨w64 Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  have aD (hp : 0 < sl t.mem Src i) : w64 (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)) =
      w64 Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (w64 Src) i) := w64_add (by omega)
  have hsp := slicePre_of h hi hu
  refine WP.seq (WP.mono (copySlice_wp u hsp) fun u₂ ⟨m₂, r2₂, kp₂⟩ => ?_)
  obtain ⟨u₃, run₃, r0₃, lr₃, z₃, g₃, m₃, rd₃, wr₃⟩ :=
    next_ok u₂ (w := cnt - i) (by rw [kp₂.gpr _ (by decide), hu.esi]) (by rw [kp₂.gpr _ (by decide), hu.ebx])
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (w64 (sb t.mem Src i)) (sl t.mem Src i) =
      bytesAt t.mem (w64 (sb t.mem Src i)) (sl t.mem Src i) := by
    refine Proof.Cmac.bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨⟨?_, ?_, ?_, ?_, hu.keep.trans (kp₂.gkeeps.trans
    ⟨fun r hr => g₃ r (by intro e; subst e; simp [gatherRegs] at hr) (by intro e; subst e; simp [gatherRegs] at hr),
      rd₃, wr₃⟩)⟩, ?_⟩
  · rw [r0₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  · rw [lr₃, pred_count hi hc]
  · rw [g₃ _ (by decide) (by decide), r2₂, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← gl_succ hdw hi]
  · rw [m₃, m₂, hbytes, hu.mem, pt_succ hdw hi]
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp, ← hlen, writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)]
    · have h0 : sl t.mem Src i = 0 := by omega
      rw [h0]; simp [bytesAt, writeBytes_nil]
  · rw [z₃, pred_beq hi hc]

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (t : State) {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' =>
      t'.mem = writeBytes t.mem (w64 Dst) (gathered 32 t.mem (w64 Src) cnt) ∧ GKeeps t t' := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.mono (body_wp h hi hu) fun u₃ ⟨h₃, z₃⟩ => ?_
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = cnt) := by
    show u₃.zf.map (!·) = _; rw [z₃]; rfl
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

/-- `GatherPre` in a state with the same registers, memory and permissions. -/
theorem GatherPre.of_eq {t t' : State} {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    GatherPre t' Src Dst cnt L := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩ := h
  exact ⟨by rw [hg]; exact a₁, by rw [hg]; exact a₂, by rw [hg]; exact a₃, a₄, a₅, a₆, by rw [hm]; exact a₇,
    by rw [hrd, hwr]; exact a₈, by rw [hm, hrd, hwr]; exact a₉, by rw [hm]; exact a₁₀, by rw [hwr]; exact a₁₁, a₁₂,
    by rw [hm]; exact a₁₃⟩

/-- `cmp ebx, 0`: only the flags change. -/
theorem cmp_ok (t : State) {cnt : Nat} (hb : t.gpr .ebx = BitVec.ofNat 32 cnt) (hc : cnt < 2 ^ 32) :
    ∃ t₁, runBlock isa [.alu .cmp .ebx (imm 0)] t = some t₁ ∧ t₁.zf = some (decide (cnt = 0)) ∧
      t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, hb, BitVec.sub_zero, VG.X86.Wp.ofNat_beq_zero hc]
  all_goals rfl

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (t : State) {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' =>
      t'.mem = writeBytes t.mem (w64 Dst) (gathered 32 t.mem (w64 Src) cnt) ∧ GKeeps t t' := by
  obtain ⟨t₁, run₁, z₁, g₁, m₁, rd₁, wr₁⟩ := cmp_ok t h.ebx h.hcnt
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (cnt = 0)) z₁ (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by rw [m₁]; simp [gathered, Sig.listed, writeBytes_nil],
      ⟨fun r _ => by rw [g₁], rd₁, wr₁⟩⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    refine WP.mono (gatherLoop_wp t₁ (h.of_eq g₁ m₁ rd₁ wr₁) (by omega)) fun t' ⟨m, k⟩ => ⟨?_, ?_⟩
    · rw [m, m₁]
    · exact ⟨fun r hr => by rw [k.gpr r hr, g₁], k.rd.trans rd₁, k.wr.trans wr₁⟩

/-! ## A frame of stack -/

/-- The state after reserving `bytes` bytes of stack. -/
def allocated (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 bytes) with
    wr := ⟨w64 (s.gpr .esp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr }

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

@[simp] theorem allocated_esp (n : Nat) (s : State) : (allocated n s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 n := by
  simp [allocated, gpr_setReg]
theorem allocated_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (allocated n s).gpr r = s.gpr r := by
  simp [allocated, gpr_setReg, h]
@[simp] theorem allocated_mem (n : Nat) (s : State) : (allocated n s).mem = s.mem := rfl
@[simp] theorem allocated_rd (n : Nat) (s : State) : (allocated n s).rd = s.rd := rfl
@[simp] theorem allocated_wr (n : Nat) (s : State) :
    (allocated n s).wr = ⟨w64 (s.gpr .esp - BitVec.ofNat 32 n), n⟩ :: s.wr := rfl

end VG.Proof.AesGcm.X86.Gather
