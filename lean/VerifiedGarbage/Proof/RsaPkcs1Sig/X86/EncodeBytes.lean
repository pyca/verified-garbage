module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Byte-exact encoding writes and register preservation on i686 -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.X86

def clob : List Reg := [.eax, .ebx, .esi, .edi, .ebp]

structure Buf (s0 : State) (k : Nat) : Prop where
  fit : (s0.gpr .edi).toNat + k ≤ 2 ^ 32
  writable : ∀ i < k, InRegions s0.wr (byteAddr (s0.gpr .edi + BitVec.ofNat 32 i)) 1

structure W (s0 : State) (acc : List Byte) (s : State) : Prop where
  rest : Keeps clob s0 s
  mem : s.mem = writeBytes s0.mem (byteAddr (s0.gpr .edi)) acc
  cursor : s.gpr .edi = s0.gpr .edi + BitVec.ofNat 32 acc.length

theorem W.after {s0 s t : State} {acc : List Byte} {regs : List Reg}
    (h : W s0 acc s) (rest : Keeps regs s t) (incl : ∀ r ∈ regs, r ∈ clob)
    (mem : t.mem = s.mem) (cursor : t.gpr .edi = s.gpr .edi) : W s0 acc t :=
  ⟨h.rest.trans (rest.mono incl), mem.trans h.mem, cursor.trans h.cursor⟩

theorem putByte_ok {s0 s : State} {k : Nat} {acc : List Byte}
    (buf : Buf s0 k) (hl : acc.length < k) (b : Byte) (h : W s0 acc s) :
    WP isa (.block (putByte b)) s fun t =>
      W s0 (acc ++ [b]) t ∧ Keeps [.eax, .edi] s t := by
  unfold putByte
  refine wp_movS rfl fun u U _ => ?_
  have writable : InRegions u.wr (byteAddr (s.gpr .edi)) 1 := by
    rw [U.wr, h.rest.2.2, h.cursor]
    exact buf.writable acc.length hl
  refine wp_storeByte (a := byteAddr (s.gpr .edi))
    (by change (u.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = _
        rw [U.other .edi (by decide)]; simp only [BitVec.add_zero]; rfl)
    writable fun v V => ?_
  refine wp_addS rfl fun t T _ => WP.block_nil ?_
  have rest : Keeps [.eax, .edi] s t :=
    (U.keeps.mono (by decide)).trans ((V.keeps _).trans (T.keeps.mono (by decide)))
  refine ⟨⟨h.rest.trans (rest.mono (by decide)), ?_, ?_⟩, rest⟩
  · rw [T.mem, V.mem, U.mem]
    change s.mem.writeW (byteAddr (s.gpr .edi)) ((u.gpr .eax).setWidth 8) = _
    rw [U.gpr, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq]
    rw [h.mem, h.cursor, byteAddr_add (by have := buf.fit; omega)]
    exact (writeBytes_snoc _ _ _ _ (by have := buf.fit; omega)).symm
  · rw [T.gpr, V.gpr, U.other .edi (by decide), h.cursor]
    simp only [List.length_append, List.length_singleton]
    rw [BitVec.add_assoc]
    change s0.gpr .edi + (BitVec.ofNat 32 acc.length + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]

theorem putBytes_ok {s0 : State} {k : Nat} (buf : Buf s0 k) (bs : List Byte) :
    ∀ {acc : List Byte} {s : State}, acc.length + bs.length ≤ k → W s0 acc s →
      WP isa (.block (putBytes bs)) s fun t => W s0 (acc ++ bs) t ∧ Keeps [.eax, .edi] s t := by
  induction bs with
  | nil => intro acc s _ h; exact WP.block_nil ⟨by simpa using h, Keeps.refl _ _⟩
  | cons b bs ih =>
    intro acc s bound h
    simp only [putBytes, List.flatMap_cons]
    refine WP.block_append (WP.mono (putByte_ok buf (by simp only [List.length_cons] at bound; omega) b h)
      fun u ⟨hu, ku⟩ => ?_)
    have next : (acc ++ [b]).length + bs.length ≤ k := by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at bound
      omega
    refine WP.mono (ih next hu) fun t ⟨ht, kt⟩ => ?_
    exact ⟨by simpa only [List.append_assoc, List.singleton_append] using ht, ku.trans kt⟩

end VG.Proof.RsaPkcs1Sig.X86
