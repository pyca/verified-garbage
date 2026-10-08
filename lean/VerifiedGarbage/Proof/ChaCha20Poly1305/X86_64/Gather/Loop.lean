import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
import VerifiedGarbage.Proof.Gcm.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: gathering the slices

Untrusted: everything here is checked by Lean. `gather` copies the `cnt`
slices that the descriptors at `r11` list, one after the other, to `rdi`
(`gather_wp`): with `i` of them copied (`GInv`), `r11` is at descriptor `i`,
`r9` holds `cnt - i`, `rdi` is `gatheredLen` of the first `i` past `dst`,
and the memory is the one on entry with their concatenation (`gathered`)
written at `dst`. The descriptors and the slices are apart from `dst`, so
they are what they were on entry. Descriptor `i` is at `Src + 16i`: the
slice's address (`sb`), then its length (`sl`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (copyBytes next advance gatherLoop gather)
open VG.Proof.AesGcm.X86_64 (ofNat_add_ofNat ofNat_sub sub_beq length_bytesAt bytesAt_frame imm_eq offset_nat)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.rax, .rcx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- What the gathering keeps: the other registers and the permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

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
  r11 : t.gpr .r11 = Src
  r9 : t.gpr .r9 = BitVec.ofNat 64 cnt
  rdi : t.gpr .rdi = Dst
  hcnt : cnt < 2 ^ 64
  dw : Src.toNat + cnt * 16 ≤ 2 ^ 64
  lt : L < 2 ^ 63
  len : gatheredLen 64 t.mem Src cnt = L
  dsr : Covers [⟨Src, cnt * 16⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, Covers [r] (t.rd ++ t.wr)
  dw' : Covers [⟨Dst, L⟩] t.wr
  dsd : (⟨Src, cnt * 16⟩ : Region).Disjoint ⟨Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, r.Disjoint ⟨Dst, L⟩

/-- `GatherPre`, in a state with the same registers, memory and permissions. -/
theorem GatherPre.of_eq {t t' : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    GatherPre t' Src Dst cnt L :=
  { h with r11 := by rw [hg, h.r11], r9 := by rw [hg, h.r9], rdi := by rw [hg, h.rdi],
           len := by rw [hm, h.len], dsr := by rw [hrd, hwr]; exact h.dsr,
           lsr := by rw [hrd, hwr, hm]; exact h.lsr, dw' := by rw [hwr]; exact h.dw',
           lsd := by rw [hm]; exact h.lsd }

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  r11 : u.gpr .r11 = Src + BitVec.ofNat 64 (16 * i)
  r9 : u.gpr .r9 = BitVec.ofNat 64 (cnt - i)
  rdi : u.gpr .rdi = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

/-- After `next`: descriptor `i` loaded. -/
structure NInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  r11 : u.gpr .r11 = Src + BitVec.ofNat 64 (16 * (i + 1))
  r9 : u.gpr .r9 = BitVec.ofNat 64 (cnt - i)
  rdi : u.gpr .rdi = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  rsi : u.gpr .rsi = sb t.mem Src i
  rcx : u.gpr .rcx = BitVec.ofNat 64 (sl t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.r11]; simp, by rw [h.r9, Nat.sub_zero], by rw [h.rdi]; simp [gatheredLen, Sig.listed],
    by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩

theorem next_ok (u : State) {A : Addr} (h11 : u.gpr .r11 = A) (r₁ : InRegions (u.rd ++ u.wr) A 8)
    (r₂ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 8) 8) :
    WP isa (.block next) u fun u' => u'.gpr .rsi = u.mem.readW A 64 ∧
      u'.gpr .rcx = u.mem.readW (A + BitVec.ofNat 64 8) 64 ∧ u'.gpr .r11 = A + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧
      u'.rd = u.rd ∧ u'.wr = u.wr := by
  have r₀ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 0) 8 := by rw [BitVec.add_zero]; exact r₁
  have i16 := imm_eq (n := 16) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [next, h11, r₀, r₂, i16], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags],
    fun r a b c => by simp [gpr_setReg, gpr_arithFlags, a, b, c], by simp [mem_setReg, mem_arithFlags],
    by simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags]⟩

theorem ofNat_beq_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rfl

theorem advance_ok (u : State) {D : Addr} {n k : Nat} (hdi : u.gpr .rdi = D) (hcx : u.gpr .rcx = BitVec.ofNat 64 n)
    (h9 : u.gpr .r9 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    WP isa (.block advance) u fun u' => u'.gpr .rdi = D + BitVec.ofNat 64 n ∧
      u'.gpr .r9 = BitVec.ofNat 64 (k - 1) ∧ u'.zf = some (decide (k - 1 = 0)) ∧
      (∀ r, r ≠ .rdi → r ≠ .r9 → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have i1 := imm_eq (n := 1) (by decide)
  have e : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := ofNat_sub hk hk'
  apply WP.of_runBlock
  refine ⟨_, by xrun [advance, hdi, hcx, h9, i1, e], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags], ?_,
    fun r a b => by simp [gpr_setReg, gpr_arithFlags, a, b], by simp [mem_setReg, mem_arithFlags],
    by simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags]⟩
  simp only [zf_setReg, zf_arithFlags]
  rw [ofNat_beq_zero (by omega)]

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
  refine WP.mono (next_ok u hu.r11 (hin _ (by omega)) (by rw [ha8]; exact hin _ (by omega)))
    fun u₁ ⟨rsi₁, rcx₁, r11₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [desc_of h hfr _ (by omega)] at rsi₁
  rw [ha8, desc_of h hfr _ (by omega), ← ha8] at rcx₁
  exact ⟨by rw [r11₁, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ],
    by rw [g₁ _ (by decide) (by decide) (by decide), hu.r9], by rw [g₁ _ (by decide) (by decide) (by decide), hu.rdi],
    rsi₁, by rw [rcx₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [m₁, hu.mem],
    hu.keep.trans ⟨fun r hr => g₁ r (by intro e; subst e; simp [gatherRegs] at hr)
      (by intro e; subst e; simp [gatherRegs] at hr) (by intro e; subst e; simp [gatherRegs] at hr), rd₁, wr₁⟩⟩

/-- What the copy of slice `i` needs, after `next`. -/
theorem copyPre_of (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    CopyPre u (sb t.mem Src i) (Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)) (sl t.mem Src i) := by
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega)
  rw [gl_succ] at hgl
  have hmem := slice_mem t.mem Src hi
  have hsub : (⟨Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i), sl t.mem Src i⟩ : Region).Sub ⟨Dst, L⟩ :=
    Offset.sub_base _ hgl
  exact ⟨hu.rsi, hu.rdi, hu.rcx, by omega, by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem,
    by rw [hu.keep.wr]; exact Proof.AesGcm.X86_64.covers_off h.dw' hgl (by omega), (h.lsd _ hmem).sub_right hsub⟩

theorem rest_wp (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    WP isa (.seq copyBytes (.block advance)) u fun u' =>
      GInv t u' Src Dst cnt (i + 1) ∧ u'.zf = some (decide (i + 1 = cnt)) := by
  have hc := h.hcnt
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 64 t.mem Src i).length = gatheredLen 64 t.mem Src i := Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ] at hgl
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hsd : (⟨sb t.mem Src i, sl t.mem Src i⟩ : Region).Disjoint ⟨Dst, L⟩ := h.lsd _ (slice_mem t.mem Src hi)
  have hcp := copyPre_of h hi hu
  refine WP.seq (WP.mono (copyBytes_ok u hcp) fun u₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (advance_ok u₂ (D := Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i))
    (n := sl t.mem Src i) (k := cnt - i)
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.rdi])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.rcx])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.r9]) (by omega) (by omega))
    fun u₃ ⟨rdi₃, r9₃, zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (sb t.mem Src i) (sl t.mem Src i) = bytesAt t.mem (sb t.mem Src i) (sl t.mem Src i) := by
    refine bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨⟨?_, ?_, ?_, ?_, hu.keep.trans ⟨fun r hr => ?_, rd₃.trans rd₂, wr₃.trans wr₂⟩⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide), hu.r11]
  · rw [r9₃, Nat.sub_sub]
  · rw [rdi₃, BitVec.add_assoc, ← BitVec.ofNat_add, ← gl_succ]
  · rw [m₃, m₂, hbytes, hu.mem, pt_succ, ← hlen,
      writeBytes_append _ _ _ _ (by rw [hlen, length_bytesAt]; omega)]
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hr
    rw [g₃ r h₄ h₆, g₂ r h₁ h₅ h₇]
  · rw [zf₃]; congr 1; simp only [decide_eq_decide]; omega

/-- One iteration of the loop. -/
theorem body_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.seq (.block next) (.seq copyBytes (.block advance))) u fun u' =>
      GInv t u' Src Dst cnt (i + 1) ∧ u'.zf = some (decide (i + 1 = cnt)) :=
  WP.seq (WP.mono (next_wp h hi hu) fun _ h₁ => rest_wp h hi h₁)

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  have hc := h.hcnt
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.mono (body_wp h hi hu) fun u₃ ⟨h₃, z₃⟩ => ?_
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = cnt) := by show u₃.zf.map (!·) = _; rw [z₃]; rfl
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

/-- The test of `src_count`. -/
theorem cmp_ok (t : State) {cnt : Nat} (h9 : t.gpr .r9 = BitVec.ofNat 64 cnt) (hc : cnt < 2 ^ 64) :
    WP isa (.block [.alu .cmp .r9 (imm 0)]) t fun t' => t'.zf = some (decide (cnt = 0)) ∧
      t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have i0 := imm_eq (n := 0) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [h9, i0], ?_⟩
  refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl⟩
  simp only [zf_arithFlags]
  show some (BitVec.ofNat 64 cnt - BitVec.ofNat 64 0 == 0) = _
  rw [Offset.ofNat_sub_ofNat_beq hc (by decide)]

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  refine WP.seq (WP.mono (cmp_ok t h.r9 h.hcnt) fun t₁ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have h' : GatherPre t₁ Src Dst cnt L := h.of_eq g₁ m₁ rd₁ wr₁
  have kp : GKeeps t t₁ := ⟨fun r _ => by rw [g₁], rd₁, wr₁⟩
  refine WP.ite (decide (cnt = 0)) (by show t₁.zf = _; exact z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by rw [m₁]; simp [gathered, Sig.listed, writeBytes_nil], kp⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    refine WP.mono (gatherLoop_wp t₁ h' (by omega)) fun t' ⟨m', k'⟩ => ⟨?_, kp.trans k'⟩
    rw [m', m₁]

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
