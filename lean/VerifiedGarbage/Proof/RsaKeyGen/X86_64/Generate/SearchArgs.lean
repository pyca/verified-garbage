module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Clear
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The prime search's arguments

For the search of the progress' prime: `out` is `p`'s slot for `p`, `q`'s for
`q`; `p` is `p`'s slot, of `p_len` octets for `q` and none for `p`; `e` the
state's last word; the tape after the octets consumed. Its six stack
arguments in the call's frame of 48 octets below the controller's.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The search's output: `p`'s slot for `p`, `q`'s for `q`. -/
def outOf (p : GenPublic) (st : KeyProgress) : Addr := if phaseWord st.phase = 0 then p.slot 4 else p.slot 5

/-- The other prime's length: none for `p`. -/
def plenOf (p : GenPublic) (st : KeyProgress) : Nat := if phaseWord st.phase = 0 then 0 else p.L

/-- The search's stack arguments. -/
def callValues (p : GenPublic) (used : Nat) (st : KeyProgress) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (plenOf p st)), (1, p.rp + BitVec.ofNat 64 used),
    (2, BitVec.ofNat 64 (p.randLen - used)), (3, p.B), (4, BitVec.ofNat 64 (p.Z / 8)), (5, p.stp)]

theorem callValues_bound (p : GenPublic) (used : Nat) (st : KeyProgress) :
    ∀ e ∈ callValues p used st, e.1 < 20 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The search's arguments in registers. -/
def SearchRegs (p : GenPublic) (st : KeyProgress) (s : State) : Prop :=
  s.gpr .rdi = outOf p st ∧ s.gpr .rsi = BitVec.ofNat 64 p.L ∧ s.gpr .rdx = p.up ∧
    s.gpr .rcx = p.stp + BitVec.ofNat 64 48 ∧ s.gpr .r8 = BitVec.ofNat 64 8 ∧ s.gpr .r9 = p.slot 4

theorem phaseWord_le (ph : KeyPhase) : phaseWord ph ≤ 1 := by cases ph <;> simp only [phaseWord] <;> omega

theorem GenLive.frame_ld {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) {t : State} {k : Nat} (hw : t.wr = (allocated k s).wr) :
    ∀ d, d + 8 ≤ 160 → InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 d) 8 := by
  have scr := h.input.frame_scr h.wr
  intro d hd
  obtain ⟨r, hr, hc⟩ := scr.st hd
  refine ⟨r, List.mem_append_right _ ?_, hc⟩
  rw [hw]
  exact List.mem_cons_of_mem _ hr

theorem GenLive.state_ld {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) {t : State} {k : Nat}
    (hw : t.wr = (allocated k s).wr) :
    ∀ d, d + 8 ≤ 56 → InRegions (t.rd ++ t.wr) (p.stp + BitVec.ofNat 64 d) 8 := by
  intro d hd
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  refine ⟨inState original, List.mem_append_right _ ?_, by rw [hst]; exact Offset.contains_base _ hd (by omega)⟩
  rw [hw]
  exact List.mem_cons_of_mem _ (by rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites]))

/-- A read of the frame sees past a store to the call's frame below it. -/
theorem read_past_call (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 48)
    (he : e + 56 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have hF : F + BitVec.ofNat 64 e = F - BitVec.ofNat 64 48 + BitVec.ofNat 64 (48 + e) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [hF]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := 48 + e) (n := 8) (e := d) (k := 8) (Or.inr (by omega))
    (by omega) (by omega)) (by decide)

theorem read_past_call0 (m : Mem) (F : Addr) (v : BitVec 64) {e : Nat} (he : e + 56 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 48) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have := read_past_call m F v (d := 0) (by decide) he
  rwa [BitVec.add_zero] at this

theorem read_past_call00 (m : Mem) (F : Addr) (v : BitVec 64) {d : Nat} (hd : d + 8 ≤ 48) :
    (m.writeW (F - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) v).readW F 64 = m.readW F 64 := by
  have := read_past_call m F v (e := 0) hd (by decide)
  rwa [BitVec.add_zero] at this

theorem search_args_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    WP isa (.block searchArgs) (allocated 48 s) fun t =>
      SearchRegs p st t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 48 s) t := by
  have hl := h.frame_ld (t := allocated 48 s) rfl
  have hsl := h.state_ld (t := allocated 48 s) rfl
  have hl0 : InRegions ((allocated 48 s).rd ++ (allocated 48 s).wr) p.F 8 := by
    simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hsp : (allocated 48 s).gpr .rsp = p.F - BitVec.ofNat 64 48 := by rw [allocated_rsp, h.rsp]
  have hr12 : (allocated 48 s).gpr .r12 = p.F := by rw [allocated_reg _ _ _ (by decide), h.r12]
  have hF := h.input.F_toNat
  have hroom : 552 ≤ p.sp.toNat := h.input.room
  have haw : (allocated 48 s).wr = ⟨p.F - BitVec.ofNat 64 48, 48⟩ :: s.wr := by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 48, 48⟩ : Region) :: s.wr = _
    rw [h.rsp]
  have scr : Scr (allocated 48 s) (p.F - BitVec.ofNat 64 48) 48 :=
    Scr.of_mem (by rw [haw]; exact List.mem_cons_self ..) (by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 48).toNat = 48 from rfl]; omega)]
      have := h.input.top
      simp only [show (BitVec.ofNat 64 48).toNat = 48 from rfl]
      omega)
  have hs : ∀ d, d + 8 ≤ 48 → InRegions (allocated 48 s).wr (p.F - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 48 s).wr (p.F - BitVec.ofNat 64 48) 8 := by
    simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hv (j : Nat) (v : BitVec 64) (hj : (j, v) ∈ p.headers used) :
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj
  have hv0 := hv 0 p.kp (by simp [GenPublic.headers])
  have hv1 := hv 1 (BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv2 := hv 2 p.up (by simp [GenPublic.headers])
  have hv3 := hv 3 p.rp (by simp [GenPublic.headers])
  have hv4 := hv 4 (BitVec.ofNat 64 p.randLen) (by simp [GenPublic.headers])
  have hv5 := hv 5 p.B (by simp [GenPublic.headers])
  have hv6 := hv 6 (BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := hv 7 p.stp (by simp [GenPublic.headers])
  have hv8 := hv 8 (BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8
  have hph : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) :=
    h.state.phase
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have hul := h.used_le
  have hrl : p.randLen < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
  have hsub : BitVec.ofNat 64 p.randLen - BitVec.ofNat 64 used = BitVec.ofNat 64 (p.randLen - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl,
      Nat.mod_eq_of_lt (by omega : used < 2 ^ 64)]
    omega
  have h4 : BitVec.ofNat 64 p.L <<< 2 + p.kp = p.slot 4 := by
    rw [SearchInit.shl_ofNat _ _ (by omega), BitVec.add_comm]; congr 2; omega
  have h5 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (Q := fun t =>
    SearchRegs p st t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold searchArgs SearchRegs writeFrame callValues outOf plenOf
  simp only [List.foldl_cons, List.foldl_nil]
  have hph1 := phaseWord_le st.phase
  rcases (by omega : phaseWord st.phase = 0 ∨ phaseWord st.phase = 1) with hp | hp <;>
  rw [hp] at hph <;>
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, allocated_mem,
    hsp, hr12, eval, execCmov, hl0, hl 8 (by decide), hl 16 (by decide), hl 24 (by decide),
    hl 32 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hsl 32 (by decide), read_past_call, read_past_call0, read_past_call00, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hph, hsub, h4, h5, hp,
    hs0, hs 8 (by decide), hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide)] <;>
  first | exact ⟨rfl, rfl⟩ | rfl

end VG.Proof.RsaKeyGen.X86_64.Generate
