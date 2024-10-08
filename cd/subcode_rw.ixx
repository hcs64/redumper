module;
#include <array>
#include <cassert>
#include <cstdint>

export module cd.subcode_rw;

import cd.cd;

namespace gpsxre
{

namespace GF64
{

// Binary extension field GF(64), used for R-W pack P and Q parity
// ref <https://github.com/geky/gf256>

typedef uint8_t gf64;
typedef uint16_t gf64_product;

const unsigned int K = 6;       // GF(2^K)
const unsigned int N = 64;      // 2^K
const unsigned int M = 63;      // non-zero element count 2^K-1
const gf64_product POLY = 0x43; // polynomial for binary extension field: x^6+x+1
const gf64 G = 2;               // generator element: x

static constexpr gf64 multiply(gf64 v1, gf64 v2)
{
    gf64_product p = 0;
    // multiply by shift and add
    for(unsigned int i = 0; i < K; ++i)
    {
        if(v1 & (((gf64_product)1) << i))
        {
            p ^= ((gf64_product)v2) << i;
        }
    }
    // modulo by long division
    for(unsigned int i = K * 2 - 1; i >= K; --i)
    {
        if(p & (((gf64_product)1) << i))
        {
            p ^= POLY << (i - K);
        }
    }
    return p;
}

static constexpr gf64 reciprocal(gf64 v)
{
    // compute powers of v until v^i = 1, the power r=v^i-1 before that
    // is the reciprocal since r*v = 1, r == 1/v
    assert(v != 0);
    gf64 prev = 0;
    gf64 m = v;
    while(1)
    {
        prev = m;
        m = multiply(m, v);
        if(m == 1)
        {
            return prev;
        }
    }
}

// 4KB multiplication table
static constexpr auto MULTIPLY = []()
{
    std::array<std::array<gf64, N>, N> table;

    for(gf64 j = 0; j < N; ++j)
    {
        for(gf64 i = 0; i < N; ++i)
        {
            table[j][i] = multiply(j, i);
        }
    }

    return table;
}();

static constexpr auto RECIPROCAL = []()
{
    std::array<gf64, N> table;

    table[0] = 0;
    for(gf64 i = 1; i < N; ++i)
    {
        table[i] = reciprocal(i);
    }

    return table;
}();

static constexpr auto G_POW = []()
{
    std::array<gf64, N> table;

    gf64 x = 1;
    for(gf64 i = 0; i < N; ++i)
    {
        table[i] = x;
        x = multiply(x, G);
    }

    return table;
}();

}

namespace SubcodeRwParityP
{

using GF64::gf64;
using GF64::M;

const unsigned int ECC_SIZE = 4;
const unsigned int CODEWORD_SIZE = 24;

unsigned int swap_index(unsigned int i)
{
    return CODEWORD_SIZE - 1 - i;
}

void eval_syndromes(const gf64 swapped_codeword[CODEWORD_SIZE], gf64 syndromes_out[ECC_SIZE])
{
    // Evaluate codeword polynomial at the first ECC_SIZE powers of the
    // generator G. Reduce multiplies with a Chien search-style terms array,
    // seems to run a bit faster than Horner's method.
    gf64 terms[CODEWORD_SIZE];
    memcpy(terms, swapped_codeword, sizeof(terms));
    for(unsigned int j = 0; j < ECC_SIZE; ++j)
    {
        gf64 total = terms[swap_index(0)];
        for(unsigned int i = 1; i < CODEWORD_SIZE; ++i)
        {
            unsigned int swap_i = swap_index(i);
            total ^= terms[swap_i];
            if(j + 1 < ECC_SIZE)
            {
                terms[swap_i] = GF64::MULTIPLY[GF64::G_POW[i]][terms[swap_i]];
            }
        }
        syndromes_out[j] = total;
    }
}

unsigned int error_locator(const gf64 syndromes[ECC_SIZE], gf64 C_out[ECC_SIZE + 1])
{
    // Berlekamp-Massey
    // ref <https://en.wikipedia.org/wiki/Berlekamp%E2%80%93Massey_algorithm>

    gf64 *C = C_out; // estimate of error locator polynomial
    C[0] = 1;
    C[1] = 0;
    C[2] = 0;
    C[3] = 0;
    C[4] = 0;
    gf64 B[ECC_SIZE + 1] = { 1, 0, 0, 0, 0 }; // last estimate
    gf64 b_recip = 1;                         // reciprocal of last estimate's discrepancy
    unsigned int v = 0;                       // estimated number of errors

    for(unsigned int k = 0; k < ECC_SIZE; ++k)
    {
        assert(C[0] == 1);
        gf64 d = syndromes[k];
        for(unsigned int j = 1; j < v + 1; ++j)
        {
            d ^= GF64::MULTIPLY[C[j]][syndromes[k - j]];
        }

        // shift prev
        assert(B[ECC_SIZE] == 0);
        for(unsigned int i = ECC_SIZE; i > 0; --i)
        {
            B[i] = B[i - 1];
        }
        B[0] = 0;

        if(d != 0)
        {
            gf64 scale = GF64::MULTIPLY[d][b_recip];
            if(2 * v <= k)
            {
                for(unsigned int i = 0; i < ECC_SIZE + 1; ++i)
                {
                    gf64 t = C[i];
                    C[i] ^= GF64::MULTIPLY[scale][B[i]];
                    B[i] = t;
                }
                b_recip = GF64::RECIPROCAL[d];
                v = k + 1 - v;
            }
            else
            {
                for(unsigned int i = 0; i < ECC_SIZE + 1; ++i)
                {
                    C[i] ^= GF64::MULTIPLY[scale][B[i]];
                }
            }
        }
    }

    return v;
}

// Return a bit field with bit `i` set if there is likely an error in
// `swapped_codeword[i]`.
uint32_t locate_errors(const gf64 swapped_codeword[CODEWORD_SIZE])
{
    gf64 syndromes[ECC_SIZE] = { 0, 0, 0, 0 };
    eval_syndromes(swapped_codeword, syndromes);
    bool error = false;
    for(unsigned int i = 0; i < ECC_SIZE; ++i)
    {
        if(syndromes[i] != 0)
        {
            error = true;
            break;
        }
    }
    if(!error)
    {
        return 0;
    }

    gf64 C[ECC_SIZE + 1];
    unsigned int v = error_locator(syndromes, C);

    const uint32_t ALL_ERRORS = (UINT32_C(1) << CODEWORD_SIZE) - 1;
    if(v > ECC_SIZE / 2)
    {
        // Exceeded design distance, errors were not reliably located.
        return ALL_ERRORS;
    }

    // Find roots of the error locator by brute force Chien search.
    // ref <https://en.wikipedia.org/wiki/Chien_search>
    // All roots are checked, instead of only those inside the codeword,
    // because additional roots indicate that errors were not reliably located.
    uint32_t errors = 0;
    unsigned int root_count = 0;
    if(C[0] == 0)
    {
        // This condition (root at 0) may not be possible.
        return ALL_ERRORS;
    }

    gf64 terms[M];
    memcpy(terms, C, sizeof(terms));

    for(unsigned int i = 0; i < M; ++i)
    {
        gf64 total = terms[0];
        for(unsigned int j = 1; j < ECC_SIZE + 1; ++j)
        {
            total ^= terms[j];
            if(i + 1 < M)
            {
                terms[j] = GF64::MULTIPLY[GF64::G_POW[j]][terms[j]];
            }
        }

        if(total == 0)
        {
            // A root at G^-i indicates an error at location i in the codeword,
            // calculate -i mod M
            unsigned int location = i == 0 ? 0 : M - i;
            if(location >= CODEWORD_SIZE || root_count == v)
            {
                // Too many roots, or roots beyond the codeword, errors
                // were not reliably located.
                return ALL_ERRORS;
            }
            errors |= UINT32_C(1) << swap_index(location);
            root_count += 1;
        }
    }

    if(root_count != v)
    {
        // Wrong number of roots, errors were not reliably located.
        return ALL_ERRORS;
    }

    // TODO Attempt to correct errors. This may fail, giving one more chance
    // to detect that errors were not reliably located.

    return errors;
}

}

export const uint32_t CD_RW_PACK_SIZE = 24;

uint32_t deinterleave_sector_pos(int pack_i, int col)
{
    // symbols 1-3 are swapped with others
    switch(col)
    {
    case 1:
        col = 18;
        break;
    case 18:
        col = 1;
        break;

    case 2:
        col = 5;
        break;
    case 5:
        col = 2;
        break;

    case 3:
        col = 23;
        break;
    case 23:
        col = 3;
        break;
    }
    // symbols are delayed up to 7 packs
    int lookahead = col & 7;
    return (pack_i + lookahead) * CD_RW_PACK_SIZE + col;
}

export const uint32_t CD_RW_PACK_CONTEXT_SECTORS = 5;

// Check for P parity errors in all R-W packs contained in a 5 sector range.
// If there are likely errors within the center sector, return false.
export bool valid_rw_packs(const std::array<uint8_t, CD_RW_PACK_CONTEXT_SECTORS * CD_SUBCODE_SIZE> &sector_subcode_rw_packs)
{
    std::array<uint8_t, CD_RW_PACK_SIZE> pack_data;

    for(int pack_i = 0; pack_i < sector_subcode_rw_packs.size() / CD_RW_PACK_SIZE; ++pack_i)
    {
        // deinterleave
        bool touches_middle_sector = false;
        bool complete = true;
        for(int col = 0; col < CD_RW_PACK_SIZE; ++col)
        {
            int offset = deinterleave_sector_pos(pack_i, col);

            if(offset >= sector_subcode_rw_packs.size())
            {
                complete = false;
                break;
            }
            if(offset >= CD_SUBCODE_SIZE * 2 && offset < CD_SUBCODE_SIZE * 3)
            {
                touches_middle_sector = true;
            }
            pack_data[col] = sector_subcode_rw_packs[offset] & 0x3f;
        }
        if(!complete || !touches_middle_sector)
        {
            continue;
        }

        uint32_t errors = SubcodeRwParityP::locate_errors(pack_data.data());

        if(errors)
        {
            for(int col = 0; col < CD_RW_PACK_SIZE; ++col)
            {
                uint64_t err_bit = (errors >> col) & 1;
                if(!err_bit)
                {
                    continue;
                }
                int offset = deinterleave_sector_pos(pack_i, col);
                if(offset >= CD_SUBCODE_SIZE * 2 && offset < CD_SUBCODE_SIZE * 3)
                {
                    // found a bad byte in this sector
                    return false;
                }
            }
        }
    }

    return true;
}

}
