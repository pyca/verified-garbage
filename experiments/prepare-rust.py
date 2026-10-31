import pathlib,sys
root=pathlib.Path(__file__).resolve().parent
checkout=pathlib.Path(sys.argv[1]); mode=sys.argv[2]
s=(root/'original-mldsa_common.rs').read_text()
# Experimental AArch64-only key layouts; not a production API/contract change.
s='// UNPROVED prepared-key experiment; AArch64 only. Do not ship.\n'+s
s=s.replace('macro_rules! ml_dsa {', 'pub(crate) const CACHE_NTT: bool = '+str(mode=='ntt').lower()+';\n\nmacro_rules! ml_dsa {')
needle='    pk: $pk:literal,'
if needle not in s:
 print(s[:3200]);raise SystemExit('macro pattern changed')
s=s.replace(needle,'    k: $k:literal,\n    l: $l:literal,\n    eta: $eta:literal,\n'+needle)
s=s.replace('pub struct $VerifyingKey {', '#[repr(C, align(16))]\n        pub struct $VerifyingKey {').replace('pub struct $SigningKey {', '#[repr(C, align(16))]\n        pub struct $SigningKey {')
s=s.replace('bytes: [u8; $pk],','bytes: [u8; $pk + 1024 * $k],').replace('sk: [u8; $sk],','sk: [u8; $sk + 1024 * ($l + 2 * $k)],')
s=s.replace('bytes: [0; $pk],','bytes: [0; $pk + 1024 * $k],').replace('sk: [0; $sk],','sk: [0; $sk + 1024 * ($l + 2 * $k)],')
s=s.replace('''                $VerifyingKey {
                    bytes: *bytes,''','''                let mut result = $VerifyingKey {
                    bytes: [0; $pk + 1024 * $k],''')
s=s.replace('''                        tr
                    },
                }
            }

            /// The bytes of the key.''','''                        tr
                    },
                };
                result.bytes[..$pk].copy_from_slice(bytes);
                result.prepare_polynomials();
                result
            }

            fn prepare_polynomials(&mut self) {
                let mut work = core::mem::MaybeUninit::<[u64; 128]>::uninit();
                for i in 0..$k {
                    unsafe {
                        let input = self.bytes.as_ptr().add(32 + 320 * i).cast();
                        let output = self.bytes.as_mut_ptr().add($pk + 1024 * i).cast();
                        $crate::arch::mldsa::vg_mldsa_unpack_t1(input, output);
                        if $crate::mldsa_common::CACHE_NTT {
                            $crate::arch::mldsa::vg_mldsa_ntt(output, work.as_mut_ptr());
                        }
                    }
                }
                unsafe { $crate::zeroize::zeroize_raw(work.as_mut_ptr().cast(), 1024); }
            }

            /// The bytes of the key.''')
s=s.replace('''                &self.bytes
''','''                self.bytes[..$pk].try_into().unwrap()
''')
s=s.replace('&self.bytes,','self.bytes.as_ptr().cast(),').replace('&self.sk,','self.sk.as_ptr().cast(),')
s=s.replace('&mut key.vk.bytes,','key.vk.bytes.as_mut_ptr().cast(),').replace('&mut key.sk,','key.sk.as_mut_ptr().cast(),')
s=s.replace('''                Ok(key)
            }

            /// The seed''','''                key.vk.prepare_polynomials();
                key.prepare_polynomials();
                Ok(key)
            }

            fn prepare_polynomials(&mut self) {
                let mut work = core::mem::MaybeUninit::<[u64; 128]>::uninit();
                let slen = if $eta == 2 { 96 } else { 128 };
                for i in 0..($l + 2 * $k) {
                    let (offset, len, a, b) = if i < $l + $k {
                        (128 + slen * i, slen, $eta, $eta)
                    } else {
                        (128 + slen * ($l + $k) + 416 * (i - $l - $k), 416, 4095, 4096)
                    };
                    unsafe {
                        let input = self.sk.as_ptr().add(offset);
                        let output = self.sk.as_mut_ptr().add($sk + 1024 * i).cast();
                        $crate::arch::mldsa::vg_mldsa_bit_unpack(input, len, a, b, output);
                        if $crate::mldsa_common::CACHE_NTT {
                            $crate::arch::mldsa::vg_mldsa_ntt(output, work.as_mut_ptr());
                        }
                    }
                }
                unsafe { $crate::zeroize::zeroize_raw(work.as_mut_ptr().cast(), 1024); }
            }

            /// The seed''')
assert s.count('fn prepare_polynomials')==2
(checkout/'src/mldsa_common.rs').write_text(s)
for n,k,l,eta in [(44,4,4,2),(65,6,5,4),(87,8,7,2)]:
 s=(root/f'original-mldsa{n}.rs').read_text().replace('    pk: ',f'    k: {k},\n    l: {l},\n    eta: {eta},\n    pk: ')
 (checkout/f'src/mldsa{n}.rs').write_text(s)
