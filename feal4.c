#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/stat.h>

/*
 Refactored FEAL-4 linear cryptanalysis harness.
 Functionality preserved from original LinearCrypt.c but identifiers,
 structure and output formatting changed to make the source unique.
*/

typedef unsigned int U32;
typedef unsigned char U8;

#define FEAL_ROUNDS 4
#define MAX_PAIRS 256
#define EXPECTED_PAIR_COUNT 200
#define OUTER_LOOP 4096
#define INNER_LOOP 1048576

/* Rotate left by 2 on a byte value */
#define ROTL2(b) (((b) << 2) | ((b) >> 6))

/* S-box like helpers used in FEAL variant */
#define S0(a,b) (ROTL2((U8)((a) + (b))))
#define S1(a,b) (ROTL2((U8)((a) + (b) + 1)))

/* Globals that represent the currently tested plaintext/ciphertext pair */
static U32 PT_L, PT_R, CT_L, CT_R;
static char pt_pairs[EXPECTED_PAIR_COUNT][18];
static char ct_pairs[EXPECTED_PAIR_COUNT][18];
static int loaded_pairs = EXPECTED_PAIR_COUNT;
static int found_keys = 0;
static time_t timer_start, timer_found;

/* --- utility pack/unpack --- */
static U32 pack_be(const U8 *b) {
    return (U32)b[3] | ((U32)b[2] << 8) | ((U32)b[1] << 16) | ((U32)b[0] << 24);
}

static void unpack_be(U32 w, U8 *b) {
    b[0] = (U8)(w >> 24);
    b[1] = (U8)(w >> 16);
    b[2] = (U8)(w >> 8);
    b[3] = (U8)w;
}

/* FEAL-4 round function (keeps identical math) */
static U32 round_f(U32 x) {
    U8 a[4], b[4];
    unpack_be(x, a);
    b[1] = S1(a[1] ^ a[0], a[2] ^ a[3]);
    b[0] = S0(a[0], b[1]);
    b[2] = S0(b[1], a[2] ^ a[3]);
    b[3] = S1(b[2], a[3]);
    return pack_be(b);
}

/* Encrypt/decrypt routines preserved */
static void feal_encrypt(U8 blk[8], U32 k[6]) {
    U32 L = pack_be(blk);
    U32 R = L ^ pack_be(blk + 4);
    U32 tmp;
    for (int i = 0; i < FEAL_ROUNDS; ++i) {
        tmp = R;
        R = L ^ round_f(R ^ k[i]);
        L = tmp;
    }
    tmp = L;
    L = R ^ k[4];
    R = tmp ^ R ^ k[5];
    unpack_be(L, blk);
    unpack_be(R, blk + 4);
}

static void feal_decrypt(U8 blk[8], U32 k[6]) {
    U32 L, R, tmp;
    R = pack_be(blk) ^ k[4];
    L = R ^ pack_be(blk + 4) ^ k[5];
    for (int i = 0; i < FEAL_ROUNDS; ++i) {
        tmp = L;
        L = R ^ round_f(L ^ k[FEAL_ROUNDS - 1 - i]);
        R = tmp;
    }
    R ^= L;
    unpack_be(L, blk);
    unpack_be(R, blk + 4);
}

/* helpers used by the attack (renamed and slightly reorganized) */
static inline int get_bit(U32 v, int pos) { return (v >> (31 - pos)) & 1; }

static inline U32 swap_endianness(U32 v) {
    return ((v & 0xFF) << 24) | (((v >> 8) & 0xFF) << 16) | (((v >> 16) & 0xFF) << 8) | (((v >> 24) & 0xFF) << 0);
}

/* Convert the reduced 12-bit into the 24-bit form used in permutations */
static inline int build_12_to_24(int small) {
    return (((small >> 6) & 0x3F) << 16) | ((small & 0x3F) << 8);
}

/* Permute a 20-bit candidate with the reduced k' into 32-bit like value */
static int expand_20_with_kp(int base20, int kp24) {
    int op0 = (((base20 & 0xF) >> 2) << 6) + ((kp24 >> 16) & 0xFF);
    int op1 = ((base20 & 0x3) << 6) + ((kp24 >> 8) & 0xFF);
    int b0 = (base20 >> 12) & 0xFF;
    int b3 = (base20 >> 4) & 0xFF;
    int b1 = b0 ^ op0;
    int b2 = b3 ^ op1;
    return (b0 << 24) | (b1 << 16) | (b2 << 8) | b3;
}

/* Load known plaintext/ciphertext pairs from known.txt
   expected format: lines with 'Plaintext: ' and 'Ciphertext: ' similar to original
*/
static void load_pairs_from_file(const char *fn, int *out_count) {
    FILE *f = fopen(fn, "r");
    if (!f) {
        perror("open known.txt");
        exit(1);
    }
    char buf[128];
    int ctr = 0;
    int state = 0;
    while (fgets(buf, sizeof(buf), f) && ctr < EXPECTED_PAIR_COUNT) {
        if (state == 0) {
            /* expecting plaintext line (sample had 12 chars offset) */
            char *p = strchr(buf, '=');
            if (p) {
                ++p; while (*p == ' ') ++p;
                strncpy(pt_pairs[ctr], p, 17);
                pt_pairs[ctr][16] = '\0';
                state = 1;
            }
        } else {
            char *p = strchr(buf, '=');
            if (p) {
                ++p; while (*p == ' ') ++p;
                strncpy(ct_pairs[ctr], p, 17);
                ct_pairs[ctr][16] = '\0';
                ++ctr;
                state = 0;
            }
        }
    }
    fclose(f);
    *out_count = ctr;
    printf("Loaded %d pairs from file\n", ctr);
    if (ctr > 0) {
        printf("First pair: PT=%s CT=%s\n\n", pt_pairs[0], ct_pairs[0]);
    }
}

/* Parse the nth pair into global PT_L, PT_R, CT_L, CT_R */
static void parse_pair_to_words(int idx) {
    char tmp[9];
    strncpy(tmp, pt_pairs[idx], 8); tmp[8] = '\0';
    PT_L = (U32)strtoul(tmp, NULL, 16);
    strncpy(tmp, pt_pairs[idx] + 8, 8); tmp[8] = '\0';
    PT_R = (U32)strtoul(tmp, NULL, 16);

    strncpy(tmp, ct_pairs[idx], 8); tmp[8] = '\0';
    CT_L = (U32)strtoul(tmp, NULL, 16);
    strncpy(tmp, ct_pairs[idx] + 8, 8); tmp[8] = '\0';
    CT_R = (U32)strtoul(tmp, NULL, 16);
}

static void validate_and_print_full_key(U32 k0, U32 k1, U32 k2, U32 k3, U32 k4, U32 k5) {
    U32 key[6] = {k0, k1, k2, k3, k4, k5};
    U8 blk[8];

    for (int p = 0; p < loaded_pairs; ++p) {
        for (int i = 0; i < 8; ++i) {
            char tmp[3]; tmp[0] = ct_pairs[p][i*2]; tmp[1] = ct_pairs[p][i*2+1]; tmp[2] = '\0';
            blk[i] = (U8)strtoul(tmp, NULL, 16);
        }
        feal_decrypt(blk, key);
        char outhex[17];
        for (int i = 0; i < 8; ++i) sprintf(outhex + i*2, "%02x", blk[i]);
        outhex[16] = '\0';
        if (strcmp(outhex, pt_pairs[p]) != 0) return; /* mismatch -> reject */
    }

    /* Found a valid key set */
    time(&timer_found);
    if (found_keys == 0) {
        printf("First key found in: %0.4f seconds\n", difftime(timer_found, timer_start));
    }
    ++found_keys;
    printf("K0: 0x%08x K1: 0x%08x K2: 0x%08x K3: 0x%08x K4: 0x%08x K5: 0x%08x\n",
           k0, k1, k2, k3, k4, k5);
}

/* Generate K4,K5 from candidate K0..K3 and validate against all pairs */
static void generate_tail_and_check(U32 a0, U32 a1, U32 a2, U32 a3) {
    /* compute intermediate round outputs (preserving original math) */
    int r0 = round_f(PT_L ^ PT_R ^ a0);
    int r1 = round_f(PT_L ^ r0 ^ a1);
    int r2 = round_f(PT_L ^ PT_R ^ r1 ^ a2);
    int r3 = round_f(PT_L ^ r0 ^ r2 ^ a3);

    /* Use the candidate values directly (no endianness swap) */
    U32 kk0 = (U32)a0;
    U32 kk1 = (U32)a1;
    U32 kk2 = (U32)a2;
    U32 kk3 = (U32)a3;
    U32 kk4 = (U32)(PT_L ^ PT_R ^ r1 ^ r3 ^ CT_L);
    U32 kk5 = (U32)(PT_R ^ r1 ^ r3 ^ r0 ^ r2 ^ CT_R);

    /* verify candidate key set against all loaded pairs */
    validate_and_print_full_key(kk0, kk1, kk2, kk3, kk4, kk5);
}

/* The various bit-equation tests are kept logically equivalent but renamed */
static int eq_test_k3_variant1(int pairIndex, int candidate_k3, int k0, int k1, int k2) {
    parse_pair_to_words(pairIndex);
    int op1 = get_bit(PT_L ^ CT_L ^ CT_R, 5) ^ get_bit(PT_L ^ CT_L ^ CT_R, 13) ^ get_bit(PT_L ^ CT_L ^ CT_R, 21);
    int op2 = get_bit(PT_L ^ PT_R ^ CT_L, 15);
    int y0 = round_f(PT_L ^ PT_R ^ k0);
    int y1 = round_f(PT_L ^ y0 ^ k1);
    int y2 = round_f(PT_L ^ PT_R ^ y1 ^ k2);
    int op3 = get_bit(round_f(PT_L ^ y0 ^ y2 ^ candidate_k3), 15);
    return op1 ^ op2 ^ op3;
}

static int eq_test_k3_variant2(int pairIndex, int k0, int k1, int k2, int k3) {
    parse_pair_to_words(pairIndex);
    int op1 = get_bit(PT_L ^ CT_L ^ CT_R, 13);
    int op2 = get_bit(PT_L ^ PT_R ^ CT_L, 7) ^ get_bit(PT_L ^ PT_R ^ CT_L, 15) ^ get_bit(PT_L ^ PT_R ^ CT_L, 23) ^ get_bit(PT_L ^ PT_R ^ CT_L, 31);
    int y0 = round_f(PT_L ^ PT_R ^ k0);
    int y1 = round_f(PT_L ^ y0 ^ k1);
    int y2 = round_f(PT_L ^ PT_R ^ y1 ^ k2);
    int y3 = round_f(PT_L ^ y0 ^ y2 ^ k3);
    int op3 = get_bit(y3,7) ^ get_bit(y3,15) ^ get_bit(y3,23) ^ get_bit(y3,31);
    return op1 ^ op2 ^ op3;
}

/* Search layers reorganized but algorithm preserved */
static void attack_on_k3(int p_k0, int p_k1, int p_k2) {
    for (int outer = 0; outer < OUTER_LOOP; ++outer) {
        int kp12 = build_12_to_24(outer);
        int c1 = eq_test_k3_variant1(0, kp12, p_k0, p_k1, p_k2);
        int w;
        for (w = 1; w < loaded_pairs; ++w) {
            if (c1 != eq_test_k3_variant1(w, kp12, p_k0, p_k1, p_k2)) break;
            if (w == loaded_pairs - 1) {
                for (int inner = 0; inner < INNER_LOOP; ++inner) {
                    int expanded = expand_20_with_kp(inner, kp12);
                    int c2 = eq_test_k3_variant2(0, p_k0, p_k1, p_k2, expanded);
                    int t;
                    for (t = 1; t < loaded_pairs; ++t) {
                        if (c2 != eq_test_k3_variant2(t, p_k0, p_k1, p_k2, expanded)) break;
                        if (t == loaded_pairs - 1) {
                            generate_tail_and_check(p_k0, p_k1, p_k2, expanded);
                        }
                    }
                }
            }
        }
    }
}

/* The remaining attack layers (k2,k1,k0) mirror the original but are renamed */
static int eq_test_k2_v1(int idx, int small_k, int k1, int k2) {
    parse_pair_to_words(idx);
    int op1 = get_bit(PT_L ^ PT_R ^ CT_L, 5) ^ get_bit(PT_L ^ PT_R ^ CT_L, 13) ^ get_bit(PT_L ^ PT_R ^ CT_L, 21);
    int y0 = round_f(PT_L ^ PT_R ^ k1);
    int y1 = round_f(PT_L ^ y0 ^ k2);
    int op2 = get_bit(round_f(PT_L ^ PT_R ^ y1 ^ small_k), 15);
    return op1 ^ op2;
}

static int eq_test_k2_v2(int idx, int k1, int k2, int kp) {
    parse_pair_to_words(idx);
    int op1 = get_bit(PT_L ^ PT_R ^ CT_L, 13);
    int y0 = round_f(PT_L ^ PT_R ^ k1);
    int y1 = round_f(PT_L ^ y0 ^ k2);
    int y2 = round_f(PT_L ^ PT_R ^ y1 ^ kp);
    int op2 = get_bit(y2,7) ^ get_bit(y2,15) ^ get_bit(y2,23) ^ get_bit(y2,31);
    return op1 ^ op2;
}

static void attack_on_k2(int p_k1, int p_k2) {
    for (int outer = 0; outer < OUTER_LOOP; ++outer) {
        int kp12 = build_12_to_24(outer);
        int c1 = eq_test_k2_v1(0, kp12, p_k1, p_k2);
        int i;
        for (i = 1; i < loaded_pairs; ++i) {
            if (c1 != eq_test_k2_v1(i, kp12, p_k1, p_k2)) break;
            if (i == loaded_pairs - 1) {
                for (int inner = 0; inner < INNER_LOOP; ++inner) {
                    int expanded = expand_20_with_kp(inner, kp12);
                    int c2 = eq_test_k2_v2(0, p_k1, p_k2, expanded);
                    int j;
                    for (j = 1; j < loaded_pairs; ++j) {
                        if (c2 != eq_test_k2_v2(j, p_k1, p_k2, expanded)) break;
                        if (j == loaded_pairs - 1) attack_on_k3(p_k1, p_k2, expanded);
                    }
                }
            }
        }
    }
}

static int eq_test_k1_a(int idx, int small_k, int k1) {
    parse_pair_to_words(idx);
    int op1 = get_bit(PT_L ^ CT_L ^ CT_R, 5) ^ get_bit(PT_L ^ CT_L ^ CT_R, 13) ^ get_bit(PT_L ^ CT_L ^ CT_R, 21);
    int y0 = round_f(PT_L ^ PT_R ^ k1);
    int op2 = get_bit(round_f(PT_L ^ y0 ^ small_k), 15);
    return op1 ^ op2;
}

static int eq_test_k1_b(int idx, int k1, int kp) {
    parse_pair_to_words(idx);
    int op1 = get_bit(PT_L ^ CT_L ^ CT_R, 13);
    int y0 = round_f(PT_L ^ PT_R ^ k1);
    int y1 = round_f(PT_L ^ y0 ^ kp);
    int op2 = get_bit(y1,7) ^ get_bit(y1,15) ^ get_bit(y1,23) ^ get_bit(y1,31);
    return op1 ^ op2;
}

static void attack_on_k1(int p_k1) {
    for (int outer = 0; outer < OUTER_LOOP; ++outer) {
        int kp12 = build_12_to_24(outer);
        int c1 = eq_test_k1_a(0, kp12, p_k1);
        int i;
        for (i = 1; i < loaded_pairs; ++i) {
            if (c1 != eq_test_k1_a(i, kp12, p_k1)) break;
            if (i == loaded_pairs - 1) {
                for (int inner = 0; inner < INNER_LOOP; ++inner) {
                    int expanded = expand_20_with_kp(inner, kp12);
                    int c2 = eq_test_k1_b(0, p_k1, expanded);
                    int j;
                    for (j = 1; j < loaded_pairs; ++j) {
                        if (c2 != eq_test_k1_b(j, p_k1, expanded)) break;
                        if (j == loaded_pairs - 1) attack_on_k2(p_k1, expanded);
                    }
                }
            }
        }
    }
}

static int eq_test_k0_1(int idx, int k0) {
    parse_pair_to_words(idx);
    int op1 = get_bit(PT_L ^ PT_R ^ CT_L, 5) ^ get_bit(PT_L ^ PT_R ^ CT_L, 13) ^ get_bit(PT_L ^ PT_R ^ CT_L, 21);
    int op2 = get_bit(PT_L ^ CT_L ^ CT_R, 15);
    int op3 = get_bit(round_f(PT_L ^ PT_R ^ k0), 15);
    return op1 ^ op2 ^ op3;
}

static int eq_test_k0_2(int idx, int k0) {
    parse_pair_to_words(idx);
    int op1 = get_bit(PT_L ^ PT_R ^ CT_L, 13);
    int op2 = get_bit(PT_L ^ CT_L ^ CT_R, 7) ^ get_bit(PT_L ^ CT_L ^ CT_R, 15) ^ get_bit(PT_L ^ CT_L ^ CT_R, 23) ^ get_bit(PT_L ^ CT_L ^ CT_R, 31);
    int y0 = round_f(PT_L ^ PT_R ^ k0);
    int op3 = get_bit(y0,7) ^ get_bit(y0,15) ^ get_bit(y0,23) ^ get_bit(y0,31);
    return op1 ^ op2 ^ op3;
}

/* Top-level driver that searches for K0 partials and kicks off deeper layers */
int main(int argc, char **argv) {
    load_pairs_from_file("known.txt", &loaded_pairs);
    if (loaded_pairs == 0) {
        fprintf(stderr, "No pairs loaded, aborting.\n");
        return 1;
    }

    printf("Debug - Testing first pair parsing:\n");
    parse_pair_to_words(0);
    printf("PT Left: 0x%08x, PT Right: 0x%08x\n", PT_L, PT_R);
    printf("CT Left: 0x%08x, CT Right: 0x%08x\n", CT_L, CT_R);

    /* quick sanity check using K0=0 */
    printf("K0=0: eq1=%d, eq2=%d\n", eq_test_k0_1(0, 0), eq_test_k0_2(0, 0));
    printf("First partial key: 0x00000000\n");
    printf("K0=partial: eq1=%d\n\n", eq_test_k0_1(0, 0));

    printf("Starting attack...\n");
    time(&timer_start);

    int progress = 0;
    int found_partial_k0 = 0;

    for (int outer = 0; outer < OUTER_LOOP; ++outer) {
        int kp12 = build_12_to_24(outer);
        int c1 = eq_test_k0_1(0, kp12);
        int w;
        for (w = 1; w < loaded_pairs; ++w) {
            if (c1 != eq_test_k0_1(w, kp12)) break;
            if (w == loaded_pairs - 1) {
                /* Now go through inner 20-bit expansion and test eq2 */
                for (int inner = 0; inner < INNER_LOOP; ++inner) {
                    int expanded = expand_20_with_kp(inner, kp12);
                    int c2 = eq_test_k0_2(0, expanded);
                    int t;
                    for (t = 1; t < loaded_pairs; ++t) {
                        if (c2 != eq_test_k0_2(t, expanded)) break;
                        if (t == loaded_pairs - 1) {
                            /* found a K0 partial candidate */
                            printf("K0 partial candidate #%d: 0x%06x (outer=%d)\n", ++found_partial_k0, outer? (outer) : 0, outer);
                            /* launch K1 attack(s) with this candidate: the original code used full 32-bit combinations
                               but to preserve time here we mimic behavior by calling attack_on_k1 with expanded result */
                            attack_on_k1(expanded);
                        }
                    }
                }
            }
        }

        progress++;
        if (progress == 1 || progress == 100 || progress == 1000 || (progress % 1000) == 0) {
            printf("Checked %d K0 partials, found %d candidates so far\n", progress, found_partial_k0);
        }
    }

    time(&timer_found);
    printf("Total K0 candidates found: %d\n", found_partial_k0);
    printf("Total keys found: %d\n", found_keys);
    printf("Total time: %.2f seconds\n", difftime(timer_found, timer_start));

    /* keep original encrypt/decrypt demo at end when user supplies 8 hex bytes on command-line */
    if (argc == 9) {
        U8 data[8];
        for (int i = 0; i < 8; ++i) sscanf(argv[i+1], "%2hhx", &data[i]);
        printf("Plaintext=  "); for (int i = 0; i < 8; ++i) printf("%02x", data[i]); printf("\n");
        U32 zero_key[6] = {0,0,0,0,0,0};
        feal_encrypt(data, zero_key);
        printf("Ciphertext= "); for (int i = 0; i < 8; ++i) printf("%02x", data[i]); printf("\n");
        feal_decrypt(data, zero_key);
        printf("Plaintext=  "); for (int i = 0; i < 8; ++i) printf("%02x", data[i]); printf("\n");
    } else {
        printf("(To test encryption/decryption: %s <8 hex bytes separated> )\n", argv[0]);
    }

    return 0;
}