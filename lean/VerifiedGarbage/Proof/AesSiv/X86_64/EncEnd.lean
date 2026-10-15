module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Enc
public import VerifiedGarbage.Proof.AesSiv.X86_64.Seal
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesSiv.X86_64.Call
import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-SIV on x86-64: the whole of `vg_aes_siv_encrypt`

`Enc.lean`'s start of `encrypt`, followed by its end, `sealTail_wp`. This is
a module of its own so that `Enc.lean` builds alongside `Seal.lean`, which it
does not otherwise need (`DecEnd.lean` is the same for `decrypt`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (bytesAt_frame k0 UpdateImpl)

variable {s₀ : State} {C A P W D : Addr} {R N L : Nat} {T : Addr}

/-- `encrypt` but for the copy of the IV: the IV at `W`, the ciphertext at
`P`, and nothing written but the data, the working space, `D` and the stack. -/
theorem encryptCore_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) :
    WP isa (encryptCore v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Frame (allRegions W D P L (s₀.gpr .rsp)) s₀.mem s'.mem ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega_arith
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  obtain ⟨sub₁, sub₂⟩ := h.all_sub
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.mono (sealTail_wp v e h.cp h.pw hs.spre hs.saved)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, (hs.frame.sub sub₁).trans (f'.sub sub₂), ?_⟩)
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide), hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega_arith), hs.acc] at out'
    rw [Spec.Siv.encryptWith_eq]
    exact out'

/-- `encryptCore` ends where the copy of the IV can read its stack arguments. -/
theorem encryptCore_out (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    WP isa (encryptCore v.callee v.ctr.callee v.ctr.suffix) s₀ (OutPre s₀ W T) :=
  WP.mono (WP.rdwr (encryptCore_wp v h)) fun _ ⟨⟨g, f, _⟩, rd, wr⟩ => outPre_of h hT g f rd wr

theorem encrypt_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L)
    (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) :
    WP isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem P L) =
        (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
  have e := h.env
  refine WP.seq (WP.mono (WP.rdwr (encryptCore_wp v h)) fun u ⟨⟨⟨g, ret⟩, f, out⟩, rd, wr⟩ => ?_)
  have hu := outPre_of h hT ⟨g, ret⟩ f rd wr
  have iW (d : Nat) (hd : d + 8 ≤ 16) : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 d) 8 :=
    e.inRW rd wr (by omega_arith)
  have oT (d : Nat) (hd : d + 8 ≤ 16) : InRegions u.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := hT.wT; omega_arith)⟩
  obtain ⟨u', run, m', g', -, -⟩ := sivOut_ok hu.a8 hu.a16 hu.i8 hu.i16 (iW 0 (by decide)) (iW 8 (by decide))
    (oT 0 (by decide)) (oT 8 (by decide))
  refine WP.of_runBlock ⟨u', run, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g' r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
      (by rintro rfl; revert hr; decide), g r hr]
  · -- The return address, apart from `T`.
    have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [fT.readW (Region.contains_self _ _) (one_out hT.ret_t) (by decide), ret]
  · have fT : Frame [⟨T, 16⟩] u.mem u'.mem := by rw [m']; exact Proof.CmacAes.X86_64.frame_store2' T _ _
    rw [out, bytesAt_frame fT (one_out hT.t_p.symm) (by have := e.lt; omega_arith)]
    have sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (hT.t_w.sub_right (e.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m', k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

end VG.Proof.AesSiv.X86_64
