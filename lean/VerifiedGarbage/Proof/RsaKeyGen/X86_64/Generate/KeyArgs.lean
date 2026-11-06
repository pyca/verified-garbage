module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Classify
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The key's arguments

`n`, `d`, `p`, `q`, `dP`, `dQ` and `qInv` at the key's buffer's slots 0, 2,
4, 5, 6, 7 and 8; the exponent the state's last word; the working space. The
twelve stack arguments in the call's frame of 96 octets below the
controller's.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen

/-- The key's stack arguments. -/
def keyValues (p : GenPublic) : List (Nat × BitVec 64) :=
  [(0, p.slot 5), (1, BitVec.ofNat 64 p.L), (2, p.slot 6), (3, BitVec.ofNat 64 p.L), (4, p.slot 7),
    (5, BitVec.ofNat 64 p.L), (6, p.slot 8), (7, BitVec.ofNat 64 p.L), (8, p.stp + BitVec.ofNat 64 48),
    (9, BitVec.ofNat 64 8), (10, p.B), (11, BitVec.ofNat 64 (p.Z / 8))]

theorem keyValues_bound (p : GenPublic) : ∀ e ∈ keyValues p, 8 * e.1 + 8 ≤ 96 := by
  simp only [keyValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem keyValues_bound20 (p : GenPublic) : ∀ e ∈ keyValues p, e.1 < 20 := fun e he => by
  have := keyValues_bound p e he; omega

/-- The key's arguments in registers. -/
def KeyRegs (p : GenPublic) (s : State) : Prop :=
  s.gpr .rdi = p.kp ∧ s.gpr .rsi = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .rdx = p.slot 2 ∧
    s.gpr .rcx = BitVec.ofNat 64 (2 * p.L) ∧ s.gpr .r8 = p.slot 4 ∧ s.gpr .r9 = BitVec.ofNat 64 p.L

/-- A read of the frame sees past a store to the key call's frame below it. -/
theorem read_past_key (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 96)
    (he : e + 104 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 96 + BitVec.ofNat 64 d) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have hF : F + BitVec.ofNat 64 e = F - BitVec.ofNat 64 96 + BitVec.ofNat 64 (96 + e) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [hF]
  exact Mem.readW_writeW_sep (Offset.sep _ (d := 96 + e) (n := 8) (e := d) (k := 8) (Or.inr (by omega))
    (by omega) (by omega)) (by decide)

theorem read_past_key0 (m : Mem) (F : Addr) (v : BitVec 64) {e : Nat} (he : e + 104 ≤ 2 ^ 64) :
    (m.writeW (F - BitVec.ofNat 64 96) v).readW (F + BitVec.ofNat 64 e) 64 =
      m.readW (F + BitVec.ofNat 64 e) 64 := by
  have := read_past_key m F v (d := 0) (by decide) he
  rwa [BitVec.add_zero] at this

theorem key_args_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block keyArgs) (allocated 96 s) fun t =>
      KeyRegs p t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p) ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (allocated 96 s) t := by
  have scrF := h.scr
  have hl : ∀ d, d + 8 ≤ 160 →
      InRegions ((allocated 96 s).rd ++ (allocated 96 s).wr) (p.F + BitVec.ofNat 64 d) 8 := by
    intro d hd
    obtain ⟨r, hr, hc⟩ := scrF.st hd
    exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), hc⟩
  have hl0 : InRegions ((allocated 96 s).rd ++ (allocated 96 s).wr) p.F 8 := by
    simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hsp : (allocated 96 s).gpr .rsp = p.F - BitVec.ofNat 64 96 := by rw [allocated_rsp, h.rsp]
  have hr12 : (allocated 96 s).gpr .r12 = p.F := by rw [allocated_reg _ _ _ (by decide), h.r12]
  have hF := h.input.F_toNat
  have hroom : 552 ≤ p.sp.toNat := h.input.room
  have haw : (allocated 96 s).wr = ⟨p.F - BitVec.ofNat 64 96, 96⟩ :: s.wr := by
    show (⟨s.gpr .rsp - BitVec.ofNat 64 96, 96⟩ : Region) :: s.wr = _
    rw [h.rsp]
  have scr : Scr (allocated 96 s) (p.F - BitVec.ofNat 64 96) 96 :=
    Scr.of_mem (by rw [haw]; exact List.mem_cons_self ..) (by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (BitVec.ofNat 64 96).toNat = 96 from rfl]; omega)]
      have := h.input.top
      simp only [show (BitVec.ofNat 64 96).toNat = 96 from rfl]
      omega)
  have hs : ∀ d, d + 8 ≤ 96 → InRegions (allocated 96 s).wr (p.F - BitVec.ofNat 64 96 + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 96 s).wr (p.F - BitVec.ofNat 64 96) 8 := by
    simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hv0 := h.header (j := 0) (v := p.kp) (by simp [GenPublic.headers])
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  have hv5 := h.header (j := 5) (v := p.B) (by simp [GenPublic.headers])
  have hv6 := h.header (j := 6) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [GenPublic.headers])
  have hv7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul, BitVec.add_zero] at hv0 hv1 hv5 hv6 hv7
  obtain ⟨hL1, hL2, -⟩ := h.len_valid
  have h2 : BitVec.ofNat 64 p.L <<< 1 = BitVec.ofNat 64 (2 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h24 : p.kp + BitVec.ofNat 64 (2 * p.L) + BitVec.ofNat 64 (2 * p.L) = p.slot 4 := by
    rw [GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; omega
  have hn (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, BitVec.add_assoc, SearchInit.add_ofNat]; congr 2; rw [Nat.succ_mul]
  have h45 : p.slot 4 + BitVec.ofNat 64 p.L = p.slot 5 := hn 4
  have h56 : p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 := hn 5
  have h67 : p.slot 6 + BitVec.ofNat 64 p.L = p.slot 7 := hn 6
  have h78 : p.slot 7 + BitVec.ofNat 64 p.L = p.slot 8 := hn 7
  have h8 : (8 : BitVec 32).setWidth 64 = BitVec.ofNat 64 8 := by decide
  have h48 : BitVec.signExtend 64 (48 : BitVec 32) = BitVec.ofNat 64 48 := by decide
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun t =>
    KeyRegs p t ∧ t.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 96) (keyValues p)) ?_ rfl)
    fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨ha, hm, k⟩
  unfold keyArgs KeyRegs writeFrame keyValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, allocated_mem,
    hsp, hr12, hl0, hl 8 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide),
    read_past_key, read_past_key0, hv0, hv1, hv5, hv6, hv7, h2, h24, h45, h56, h67, h78, h8, h48,
    hs0, hs 8 (by decide), hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide),
    hs 48 (by decide), hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide),
    hs 88 (by decide)]

end VG.Proof.RsaKeyGen.X86_64.Generate
