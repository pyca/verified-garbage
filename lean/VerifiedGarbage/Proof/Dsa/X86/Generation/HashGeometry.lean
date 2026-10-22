module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash

/-! # Reuse HMAC's verified streaming-call resource geometry for seed hashing -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure HashGeometry {H : Hash} (ok : HashOK H) (st data digest scratch : BitVec 32) (len : Nat) (s : State) : Prop where
  small : len < 2 ^ 32
  sp48 : 48 ≤ (s.gpr .esp).toNat
  readable : Covers [⟨data.setWidth 64, len⟩] (s.rd ++ s.wr)
  writable : Covers [⟨st.setWidth 64, H.S⟩, ⟨digest.setWidth 64, H.F⟩, ⟨scratch.setWidth 64, ok.Wb⟩] s.wr
  st_digest : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨digest.setWidth 64, H.F⟩
  st_scratch : Region.Disjoint ⟨st.setWidth 64, H.S⟩ ⟨scratch.setWidth 64, ok.Wb⟩
  digest_scratch : Region.Disjoint ⟨digest.setWidth 64, H.F⟩ ⟨scratch.setWidth 64, ok.Wb⟩
  data_st : Region.Disjoint ⟨data.setWidth 64, len⟩ ⟨st.setWidth 64, H.S⟩
  data_digest : Region.Disjoint ⟨data.setWidth 64, len⟩ ⟨digest.setWidth 64, H.F⟩
  data_scratch : Region.Disjoint ⟨data.setWidth 64, len⟩ ⟨scratch.setWidth 64, ok.Wb⟩
  stack_st : (stk s).Disjoint ⟨st.setWidth 64, H.S⟩
  stack_data : (stk s).Disjoint ⟨data.setWidth 64, len⟩
  stack_digest : (stk s).Disjoint ⟨digest.setWidth 64, H.F⟩
  stack_scratch : (stk s).Disjoint ⟨scratch.setWidth 64, ok.Wb⟩
  st_fit : st.toNat + H.S ≤ 2 ^ 32
  data_fit : data.toNat + len ≤ 2 ^ 32
  digest_fit : digest.toNat + H.F ≤ 2 ^ 32
  scratch_fit : scratch.toNat + ok.Wb ≤ 2 ^ 32

namespace HashGeometry

theorem of_regions {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s t : State}
    (h : HashGeometry ok st data digest scratch len s) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.gpr .esp = s.gpr .esp) : HashGeometry ok st data digest scratch len t := by
  refine ⟨h.small, by rw [sp]; exact h.sp48, by rw [rd, wr]; exact h.readable,
    by rw [wr]; exact h.writable, h.st_digest, h.st_scratch, h.digest_scratch,
    h.data_st, h.data_digest, h.data_scratch, ?_, ?_, ?_, ?_, h.st_fit, h.data_fit, h.digest_fit, h.scratch_fit⟩
  all_goals change Region.Disjoint (below (t.gpr .esp) 48) _; rw [sp]
  · exact h.stack_st
  · exact h.stack_data
  · exact h.stack_digest
  · exact h.stack_scratch

theorem after {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s t : State} {ws : List Region}
    (h : HashGeometry ok st data digest scratch len s) (A : After s ws t) : HashGeometry ok st data digest scratch len t :=
  h.of_regions A.rd A.wr A.esp

end HashGeometry
end VG.Proof.Dsa.X86.Generation
