import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Copy
import VerifiedGarbage.Proof.Gcm.SealGather

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: gathering the slices

Untrusted: everything here is checked by Lean. `gather` copies the `cnt`
slices that the descriptors at `x6` list, one after the other, to `x11`
(`gather_wp`): with `i` of them copied, `x6` is at descriptor `i`, `x7`
holds `cnt - i`, `x11` is `gatheredLen` of the first `i` past `dst`, and the
memory is the one on entry with their concatenation (`gathered`) written at
`dst`. The descriptors and the slices are apart from `dst`, so they are
what they were on entry.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Impl.AesGcm.AArch64.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)
open VG.Proof.AesGcm.AArch64 (eval_zero eval_nonzero covers_off covers_of_mem)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.x6, .x7, .x11, .x12, .x13, .x14, .x15]

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
    rcases hm with e | e | e | e | e <;> simp [e])), h.sp, h.rd, h.wr⟩

section
variable (m : Mem) (Src : Addr)

/-- Slice `i`: its address and its length. -/
abbrev sb (i : Nat) : Addr := m.readW (Src + BitVec.ofNat 64 (16 * i)) 64
abbrev sl (i : Nat) : Nat := (m.readW (Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat

end

theorem desc_off (i : Nat) : i * (2 * (64 / 8)) = 16 * i := by omega

theorem gl_succ (m : Mem) (Src : Addr) (i : Nat) :
    gatheredLen 64 m Src (i + 1) = gatheredLen 64 m Src i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, desc_off]

theorem pt_succ (m : Mem) (Src : Addr) (i : Nat) :
    gathered 64 m Src (i + 1) = gathered 64 m Src i ++ bytesAt m (sb m Src i) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq]

theorem gl_mono (m : Mem) (Src : Addr) {i j : Nat} (h : i ≤ j) :
    gatheredLen 64 m Src i ≤ gatheredLen 64 m Src j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) (Src : Addr) {i cnt : Nat} (hi : i < cnt) :
    (⟨sb m Src i, sl m Src i⟩ : Region) ∈ Sig.listed 64 m .u8 Src cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  simp only [desc_off, BitVec.setWidth_eq, Elem.size, Nat.mul_one]

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : Addr) (cnt L : Nat) : Prop where
  x6 : t.gpr .x6 = Src
  x7 : t.gpr .x7 = BitVec.ofNat 64 cnt
  x11 : t.gpr .x11 = Dst
  hcnt : cnt < 2 ^ 64
  dw : Src.toNat + cnt * 16 ≤ 2 ^ 64
  lt : L < 2 ^ 64
  len : gatheredLen 64 t.mem Src cnt = L
  dsr : Covers [⟨Src, cnt * 16⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, Covers [r] (t.rd ++ t.wr)
  dw' : Covers [⟨Dst, L⟩] t.wr
  dsd : (⟨Src, cnt * 16⟩ : Region).Disjoint ⟨Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, r.Disjoint ⟨Dst, L⟩

theorem next_ok (u : State) {A : Addr} (h6 : u.gpr .x6 = A) (r₁ : InRegions (u.rd ++ u.wr) A 8)
    (r₂ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 8) 8) :
    ∃ u', runBlock isa next u = some u' ∧ u'.gpr .x12 = u.mem.readW A 64 ∧
      u'.gpr .x13 = u.mem.readW (A + BitVec.ofNat 64 8) 64 ∧ u'.gpr .x6 = A + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x6 → r ≠ .x12 → r ≠ .x13 → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.sp = u.sp ∧
      u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨((u.write .x .x12 (u.mem.read A 8)).write .x .x13 (u.mem.read (A + BitVec.ofNat 64 8) 8)).write .x .x6
      (A + BitVec.ofNat 64 16), by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, next,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      BitVec.add_zero, h6, r₁, r₂], ?_, ?_, ?_, fun r a b c => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, Mem.readW]
  · simp [gpr_write, Mem.readW]
  · simp [gpr_write]
  · simp [gpr_write, a, b, c]

theorem sub7_ok (u : State) :
    ∃ u', runBlock isa [.subImm .x .x7 .x7 1] u = some u' ∧ u'.gpr .x7 = u.gpr .x7 - 1 ∧
      (∀ r, r ≠ .x7 → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.sp = u.sp ∧ u'.rd = u.rd ∧ u'.wr = u.wr :=
  ⟨u.write .x .x7 (u.read .x .x7 - BitVec.ofNat 64 1),
    by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true, Size.bits],
    by simp [gpr_write, State.read], fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  x6 : u.gpr .x6 = Src + BitVec.ofNat 64 (16 * i)
  x7 : u.gpr .x7 = BitVec.ofNat 64 (cnt - i)
  x11 : u.gpr .x11 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

/-- After `next`: descriptor `i` loaded. -/
structure NInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  x6 : u.gpr .x6 = Src + BitVec.ofNat 64 (16 * (i + 1))
  x7 : u.gpr .x7 = BitVec.ofNat 64 (cnt - i)
  x11 : u.gpr .x11 = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  x12 : u.gpr .x12 = sb t.mem Src i
  x13 : u.gpr .x13 = BitVec.ofNat 64 (sl t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.x6]; simp, by rw [h.x7, Nat.sub_zero], by rw [h.x11]; simp [gatheredLen, Sig.listed],
    by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩

section
variable {t u : State} {Src Dst : Addr} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

omit h in
/-- What the loop has written is within `dst`. -/
theorem frame_of {xs : List Byte} (hm : u.mem = writeBytes t.mem Dst xs) (hx : xs.length ≤ L) :
    Frame [⟨Dst, L⟩] t.mem u.mem := by
  rw [hm]
  refine writeBytes_frame t.mem Dst _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]
  omega

theorem gl_le (hi : i ≤ cnt) : gatheredLen 64 t.mem Src i ≤ L := h.len ▸ gl_mono t.mem Src hi

theorem len_le (hi : i ≤ cnt) : (gathered 64 t.mem Src i).length ≤ L :=
  (Proof.Gcm.length_gathered _ _ _ _) ▸ gl_le h hi

/-- The descriptors are what they were. -/
theorem desc_of (hf : Frame [⟨Dst, L⟩] t.mem u.mem) (d : Nat) (hd : d + 8 ≤ cnt * 16) :
    u.mem.readW (Src + BitVec.ofNat 64 d) 64 = t.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨Src, cnt * 16⟩) (Offset.contains_base Src hd (by have := h.dw; omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.dsd) (by decide)

theorem next_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.block next) u (NInv t · Src Dst cnt i) := by
  have hdw := h.dw
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hin (d : Nat) (hd : d + 8 ≤ cnt * 16) : InRegions (u.rd ++ u.wr) (Src + BitVec.ofNat 64 d) 8 := by
    rw [hu.keep.rd, hu.keep.wr]; exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base Src hd (by omega)⟩
  have ha8 : Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8 = Src + BitVec.ofNat 64 (16 * i + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  obtain ⟨u₁, run₁, x12₁, x13₁, x6₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := next_ok u hu.x6 (hin _ (by omega))
    (by rw [ha8]; exact hin _ (by omega))
  rw [desc_of h hfr _ (by omega)] at x12₁
  rw [ha8, desc_of h hfr _ (by omega), ← ha8] at x13₁
  refine WP.of_runBlock ⟨u₁, run₁, ?_⟩
  exact ⟨by rw [x6₁, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ],
    by rw [g₁ _ (by decide) (by decide) (by decide), hu.x7], by rw [g₁ _ (by decide) (by decide) (by decide), hu.x11],
    x12₁, by rw [x13₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [m₁, hu.mem],
    hu.keep.trans ⟨fun r hr => g₁ r (by intro e; subst e; simp [gatherRegs] at hr)
      (by intro e; subst e; simp [gatherRegs] at hr) (by intro e; subst e; simp [gatherRegs] at hr), sp₁, rd₁, wr₁⟩⟩

theorem rest_wp (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    WP isa (.seq copySlice (.block [.subImm .x .x7 .x7 1])) u (GInv t · Src Dst cnt (i + 1)) := by
  have hc := h.hcnt
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 64 t.mem Src i).length = gatheredLen 64 t.mem Src i := Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ] at hgl
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  -- The slice.
  have hmem := slice_mem t.mem Src hi
  have hsd : (⟨sb t.mem Src i, sl t.mem Src i⟩ : Region).Disjoint ⟨Dst, L⟩ := h.lsd _ hmem
  have hsub : (⟨Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i), sl t.mem Src i⟩ : Region).Sub ⟨Dst, L⟩ :=
    Offset.sub_base _ hgl
  have hsp : SlicePre u (sb t.mem Src i) (Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)) (sl t.mem Src i) :=
    ⟨hu.x12, hu.x11, hu.x13, by omega, by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem,
      by rw [hu.keep.wr]; exact covers_off h.dw' hgl hL, hsd.sub_right hsub⟩
  refine WP.seq (WP.mono (copySlice_wp u hsp) fun u₂ ⟨m₂, x11₂, kp₂⟩ => ?_)
  obtain ⟨u₃, run₃, x7₃, g₃, m₃, sp₃, rd₃, wr₃⟩ := sub7_ok u₂
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (sb t.mem Src i) (sl t.mem Src i) = bytesAt t.mem (sb t.mem Src i) (sl t.mem Src i) := by
    refine Proof.AesGcm.AArch64.bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨?_, ?_, ?_, ?_, hu.keep.trans (kp₂.gkeeps.trans
    ⟨fun r hr => g₃ r (by intro e; subst e; simp [gatherRegs] at hr), sp₃, rd₃, wr₃⟩)⟩
  · rw [g₃ _ (by decide), kp₂.gpr _ (by decide), hu.x6]
  · rw [x7₃, kp₂.gpr _ (by decide), hu.x7, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega)]; rfl
  · rw [g₃ _ (by decide), x11₂, BitVec.add_assoc, ← BitVec.ofNat_add, ← gl_succ]
  · rw [m₃, m₂, hbytes, hu.mem, pt_succ, ← hlen,
      writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)]

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  have hc := h.hcnt
  refine WP.loop (M := isa) (c := .nonzero .x .x7)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.seq (WP.mono (next_wp h hi hu) fun u₁ h₁ => WP.mono (rest_wp h hi h₁) fun u₃ h₃ => ?_)
  have ev := eval_nonzero (r := .x7) (a := cnt - (i + 1)) h₃.x7 (by omega)
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp; omega, cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  refine WP.ite (decide (cnt = 0)) (eval_zero h.x7 h.hcnt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    exact gatherLoop_wp t h (by omega)

/-! ## Frames

Steps of the functions that gather the slices in a frame of their own. -/

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- The `n` bytes at `p + d` are within the `k` bytes at `p + e`. -/
theorem contains_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (hd : d - e < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  rw [show p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) by
    rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h₁]]
  exact Offset.contains_base _ (by omega) hd

/-- `ldrSp t k`: the doubleword at `sp + k` into `t`. -/
theorem ldrSp_ok (a : State) {t : Reg} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (r : InRegions (a.rd ++ a.wr) (a.sp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.ldrSp t k]) a fun e => e.gpr t = a.mem.read (a.sp + BitVec.ofNat 64 k) 8 ∧
      (∀ r, r ≠ t → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.sp = a.sp ∧ e.rd = a.rd ∧ e.wr = a.wr ∧ e.v = a.v := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits, Option.map_some,
      BitVec.setWidth_eq, hk, r, and_self, ite_true]; rfl, rfl⟩ fun e he => ?_
  subst he
  exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl, rfl⟩

end VG.Proof.AesGcm.AArch64.Gather
