module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Front
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Setup
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Front
import VerifiedGarbage.Proof.Ecdsa.X86_64.Setup
import VerifiedGarbage.Proof.Framework.Offset

/-! # Decode the compressed x coordinate with the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

structure DecompressPre (c : Cfg) (s : State) : Prop where
  pk : (⟨s.gpr .rsi, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr
  ws : (⟨s.gpr .rdx, size⟩ : Region) ∈ s.wr
  disjoint : Region.Disjoint ⟨s.gpr .rsi, c.C.len + 1⟩ ⟨s.gpr .rdx, size⟩
  fit : (s.gpr .rdx).toNat + size ≤ 2 ^ 64

structure DecompressStart (c : Cfg) (s₀ : State) (g : Reg → BitVec 64) (s : State) : Prop where
  scr : Scr s (s₀.gpr .rdx) size
  fixed : Fixed c (s₀.gpr .rdx) g s.mem
  original : ∀ r ∈ Cfg.saved.map Prod.fst, g r = s₀.gpr r
  out : s.gpr .rsi = s₀.gpr .rdi
  pk : s.gpr .r9 = s₀.gpr .rsi
  x : sv c (s₀.gpr .rdx) s E = keyX c s₀
  flag : word s.mem (s₀.gpr .rdx) (c.sl FLAG) = BitVec.allOnes 64
  outside : Outside (s₀.gpr .rdx) 0 size s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem decompressStart_ok {c : Cfg} (hc : BaseCfgOk c) {s₀ : State} (hp : DecompressPre c s₀)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ g s, DecompressStart c s₀ g s → WP isa rest s Q) :
    WP isa (.seq (.block Impl.EcKey.Compressed.X86_64.args)
      (.seq (.block (c.setupWith none)) rest)) s₀ Q := by
  have hsz : size = 8192 := rfl
  have := hc.len8
  have := hc.len_hi
  have := hc.n10
  refine WP.seq (WP.mono (args_ok s₀) fun s₁ ⟨r8, r9, rcx, rsi, rdx, k₁⟩ => ?_)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [k₁.2.2.1, k₁.2.2.2]
  have hsp : SetupPre c s₁ := by
    have hin : ∀ e, e + 8 ≤ c.C.len →
        InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + 1 + BitVec.ofNat 64 e) 8 := by
      intro e he
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      exact ⟨_, hp.pk, Offset.contains_base _ (by omega) (by omega)⟩
    have hd : Region.Disjoint ⟨s₀.gpr .rsi + 1, c.C.len⟩ ⟨s₀.gpr .rdx, size⟩ :=
      hp.disjoint.sub_left (Offset.sub_base _ (d := 1) (by omega))
    exact ⟨by rw [k₁.2.2.2, r8]; exact hp.ws,
      by rw [rcx, rw₁]; exact hin, by rw [rsi, rw₁]; exact hin,
      by rw [rdx, rw₁]; exact hin, by rw [rsi, r8]; exact hd,
      by rw [rdx, r8]; exact hd, by rw [rcx, r8]; exact hd, by rw [r8]; exact hp.fit⟩
  refine WP.seq (WP.mono (setup_ok hc (hs := none) (.inl rfl) hsp) fun s₂ S => ?_)
  rw [r8] at S
  apply h s₁.gpr s₂
  refine ⟨S.scr, VG.Proof.EcKey.Validate.X86_64.setup_fixed S,
    fun r hr => k₁.1 r (by revert r; decide), S.rsi.trans (k₁.1 _ (by decide)),
    (S.keep.gpr _ (by decide)).trans r9, ?_, S.flag, ?_, ?_, ?_⟩
  · rw [S.e, shAt_none, Nat.shiftRight_zero, rdx, k₁.2.1]
  · rw [← k₁.2.1]
    exact S.unch.outside (by simp)
  · rw [S.keep.rd, k₁.2.2.1]
  · rw [S.keep.wr, k₁.2.2.2]

end VG.Proof.EcKey.Compressed.X86_64
