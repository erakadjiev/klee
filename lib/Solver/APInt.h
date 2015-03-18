//===-- llvm/ADT/APInt.h - For Arbitrary Precision Integer -----*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements a class to represent arbitrary precision integral
// constant values and operations on them.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_APINTLITE_H
#define LLVM_APINTLITE_H

#include "MathExtras.h"
#include <cassert>
#include <iostream>

namespace llvm {
// An unsigned host type used as a single part of a multi-part
// bignum.
typedef uint64_t integerPart;
//const unsigned int host_char_bit = 8;
//const unsigned int integerPartWidth = host_char_bit *
//    static_cast<unsigned int>(sizeof(integerPart));  

class APIntLite{
  private:
    unsigned BitWidth;      ///< The number of bits in this APInt.
    
    /// This union is used to store the integer value. When the
    /// integer bit-width <= 64, it uses VAL, otherwise it uses pVal.
    union {
        uint64_t VAL;    ///< Used to store the <= 64 bits integer value.
        uint64_t *pVal;  ///< Used to store the >64 bits integer value.
    };
    
    /// This enum is used to hold the constants we needed for APInt.
    enum {
      /// Bits in a word
      APINT_BITS_PER_WORD = static_cast<unsigned int>(sizeof(uint64_t)) * 8,
      /// Byte size of a word
      APINT_WORD_SIZE = static_cast<unsigned int>(sizeof(uint64_t))
    };
    
    /// This constructor is used only internally for speed of construction of
    /// temporaries. It is unsafe for general use so it is not public.
    /// @brief Fast internal constructor
    APIntLite(uint64_t* val, unsigned bits) : BitWidth(bits), pVal(val) { }
    
  public:
    /// @returns true if the number of bits <= 64, false otherwise.
    /// @brief Determine if this APInt just has one word to store value.
    bool isSingleWord() const {
      return BitWidth <= APINT_BITS_PER_WORD;
    }
    
    /// Here one word's bitwidth equals to that of uint64_t.
    /// @returns the number of words to hold the integer value with a
    /// given bit width.
    /// @brief Get the number of words.
    static unsigned getNumWords(unsigned BitWidth) {
      return (BitWidth + APINT_BITS_PER_WORD - 1) / APINT_BITS_PER_WORD;
    }
    
    /// Here one word's bitwidth equals to that of uint64_t.
    /// @returns the number of words to hold the integer value of this APInt.
    /// @brief Get the number of words.
    unsigned getNumWords() const {
      return getNumWords(BitWidth);
    }
    
    /// This method is used internally to clear the to "N" bits in the high order
    /// word that are not used by the APInt. This is needed after the most
    /// significant word is assigned a value to ensure that those bits are
    /// zero'd out.
    /// @brief Clear unused high order bits
    APIntLite& clearUnusedBits() {
      // Compute how many bits are used in the final word
      unsigned wordBits = BitWidth % APINT_BITS_PER_WORD;
      if (wordBits == 0)
        // If all bits are used, we want to leave the value alone. This also
        // avoids the undefined behavior of >> when the shift is the same size as
        // the word size (64).
        return *this;
      
      // Mask out the high bits.
      uint64_t mask = ~uint64_t(0ULL) >> (APINT_BITS_PER_WORD - wordBits);
      if (isSingleWord())
        VAL &= mask;
      else
        pVal[getNumWords() - 1] &= mask;
      return *this;
    }
    
    /// A utility function for allocating memory and checking for allocation
    /// failure.  The content is not zeroed.
    inline static uint64_t* getMemory(unsigned numWords) {
      uint64_t * result = new uint64_t[numWords];
      assert(result && "APInt memory allocation fails!");
      return result;
    }
    
    /// A utility function for allocating memory, checking for allocation failures,
    /// and ensuring the contents are zeroed.
    inline static uint64_t* getClearedMemory(unsigned numWords) {
      uint64_t * result = new uint64_t[numWords];
      assert(result && "APInt memory allocation fails!");
      memset(result, 0, numWords * sizeof(uint64_t));
      return result;
    }
    
    /// out-of-line slow case for inline constructor
    void initSlowCase(unsigned numBits, uint64_t val, bool isSigned) {
      pVal = getClearedMemory(getNumWords());
      pVal[0] = val;
      if (isSigned && int64_t(val) < 0)
        for (unsigned i = 1; i < getNumWords(); ++i)
          pVal[i] = -1ULL;
    }
    
    /// out-of-line slow case for inline copy constructor
    void initSlowCase(const APIntLite& that) {
      pVal = getMemory(getNumWords());
      memcpy(pVal, that.pVal, getNumWords() * APINT_WORD_SIZE);
    }
    
    /// out-of-line slow case for operator=
    APIntLite& AssignSlowCase(const APIntLite& RHS) {
      // Don't do anything for X = X
      if (this == &RHS)
        return *this;
      
      if (BitWidth == RHS.getBitWidth()) {
        // assume same bit-width single-word case is already handled
        assert(!isSingleWord());
        memcpy(pVal, RHS.pVal, getNumWords() * APINT_WORD_SIZE);
        return *this;
      }
      
      if (isSingleWord()) {
        // assume case where both are single words is already handled
        assert(!RHS.isSingleWord());
        VAL = 0;
        pVal = getMemory(RHS.getNumWords());
        memcpy(pVal, RHS.pVal, RHS.getNumWords() * APINT_WORD_SIZE);
      } else if (getNumWords() == RHS.getNumWords())
        memcpy(pVal, RHS.pVal, RHS.getNumWords() * APINT_WORD_SIZE);
      else if (RHS.isSingleWord()) {
        delete [] pVal;
        VAL = RHS.VAL;
      } else {
        delete [] pVal;
        pVal = getMemory(RHS.getNumWords());
        memcpy(pVal, RHS.pVal, RHS.getNumWords() * APINT_WORD_SIZE);
      }
      BitWidth = RHS.BitWidth;
      return clearUnusedBits();
    }
    
    /// @name Constructors
    /// @{
    /// If isSigned is true then val is treated as if it were a signed value
    /// (i.e. as an int64_t) and the appropriate sign extension to the bit width
    /// will be done. Otherwise, no sign extension occurs (high order bits beyond
    /// the range of val are zero filled).
    /// @param numBits the bit width of the constructed APInt
    /// @param val the initial value of the APInt
    /// @param isSigned how to treat signedness of val
    /// @brief Create a new APInt of numBits width, initialized as val.
    APIntLite(unsigned numBits, uint64_t val, bool isSigned = false)
    : BitWidth(numBits), VAL(0) {
      assert(BitWidth && "bitwidth too small");
      if (isSingleWord())
        VAL = val;
      else
        initSlowCase(numBits, val, isSigned);
      clearUnusedBits();
    }
    
    /// Note that numWords can be smaller or larger than the corresponding bit
    /// width but any extraneous bits will be dropped.
    /// @param numBits the bit width of the constructed APInt
    /// @param numWords the number of words in bigVal
    /// @param bigVal a sequence of words to form the initial value of the APInt
    /// @brief Construct an APInt of numBits width, initialized as bigVal[].
    APIntLite(unsigned numBits, unsigned numWords, const uint64_t bigVal[])
    : BitWidth(numBits), VAL(0) {
      assert(BitWidth && "Bitwidth too small");
      assert(bigVal && "Null pointer detected!");
      if (isSingleWord())
        VAL = bigVal[0];
      else {
        // Get memory, cleared to 0
        pVal = getClearedMemory(getNumWords());
        // Calculate the number of words to copy
        unsigned words = std::min<unsigned>(numWords, getNumWords());
        // Copy the words from bigVal to pVal
        memcpy(pVal, bigVal, words * APINT_WORD_SIZE);
        
        std::cerr << "Words: ";
            for(unsigned i = 0; i < numWords; ++i){
              std::cerr << bigVal[i] << "->" << pVal[i] << " ";
            }
            std::cerr << "\n";
        
      }
      // Make sure unused high bits are cleared
//      clearUnusedBits();
    }
    
    /// Simply makes *this a copy of that.
    /// @brief Copy Constructor.
    APIntLite(const APIntLite& that)
      : BitWidth(that.BitWidth), VAL(0) {
        assert(BitWidth && "bitwidth too small");
        if (isSingleWord())
          VAL = that.VAL;
        else
          initSlowCase(that);
    }
    
    explicit APIntLite() : BitWidth(1) {}
    
    /// @brief Destructor.
    ~APIntLite() {
      if (!isSingleWord())
        delete [] pVal;
    }
    
    /// @}
    /// @name Assignment Operators
    /// @{
    /// @returns *this after assignment of RHS.
    /// @brief Copy assignment operator.
    APIntLite& operator=(const APIntLite& RHS) {
      // If the bitwidths are the same, we can avoid mucking with memory
      if (isSingleWord() && RHS.isSingleWord()) {
        VAL = RHS.VAL;
        BitWidth = RHS.BitWidth;
        return clearUnusedBits();
      }
      
      return AssignSlowCase(RHS);
    }
    
    /// @returns the bit position in a word for the specified bit position
    /// in the APInt.
    /// @brief Determine which bit in a word a bit is in.
    static unsigned whichBit(unsigned bitPosition) {
      return bitPosition % APINT_BITS_PER_WORD;
    }
    
    /// @returns the word position for the specified bit position.
    /// @brief Determine which word a bit is in.
    static unsigned whichWord(unsigned bitPosition) {
      return bitPosition / APINT_BITS_PER_WORD;
    }
    
    /// This method generates and returns a uint64_t (word) mask for a single
    /// bit at a specific bit position. This is used to mask the bit in the
    /// corresponding word.
    /// @returns a uint64_t with only bit at "whichBit(bitPosition)" set
    /// @brief Get a single bit mask.
    static uint64_t maskBit(unsigned bitPosition) {
      return 1ULL << whichBit(bitPosition);
    }
    
    /// @}
    /// @name Value Characterization Functions
    /// @{
    
    /// @returns the total number of bits.
    unsigned getBitWidth() const {
      return BitWidth;
    }
    
    /// @returns the bit value at bitPosition
    /// @brief Array-indexing support.
    bool operator[](unsigned bitPosition) const {
      assert(bitPosition < getBitWidth() && "Bit position out of bounds!");
      return (maskBit(bitPosition) &
          (isSingleWord() ?  VAL : pVal[whichWord(bitPosition)])) != 0;
    }
    
    /// Performs logical negation operation on this APInt.
    /// @returns true if *this is zero, false otherwise.
    /// @brief Logical negation operator.
    bool operator !() const {
      if (isSingleWord())
        return !VAL;

      for (unsigned i = 0; i < getNumWords(); ++i)
        if (pVal[i])
          return false;
      return true;
    }
    
    /// @}
    /// @name Value Tests
    /// @{
    /// This tests the high bit of this APInt to determine if it is set.
    /// @returns true if this APInt is negative, false otherwise
    /// @brief Determine sign of this APInt.
    bool isNegative() const {
      return (*this)[BitWidth - 1];
    }
    
    /// This converts the APInt to a boolean value as a test against zero.
    /// @brief Boolean conversion function.
    bool getBoolValue() const {
      return !!*this;
    }
    
    /// out-of-line slow case for countLeadingZeros
    unsigned countLeadingZerosSlowCase() const {
      // Treat the most significand word differently because it might have
      // meaningless bits set beyond the precision.
      unsigned BitsInMSW = BitWidth % APINT_BITS_PER_WORD;
      integerPart MSWMask;
      if (BitsInMSW) MSWMask = (integerPart(1) << BitsInMSW) - 1;
      else {
        MSWMask = ~integerPart(0);
        BitsInMSW = APINT_BITS_PER_WORD;
      }
      
      unsigned i = getNumWords();
      integerPart MSW = pVal[i-1] & MSWMask;
      if (MSW)
        return CountLeadingZeros_64(MSW) - (APINT_BITS_PER_WORD - BitsInMSW);
      
      unsigned Count = BitsInMSW;
      for (--i; i > 0u; --i) {
        if (pVal[i-1] == 0)
          Count += APINT_BITS_PER_WORD;
        else {
          Count += CountLeadingZeros_64(pVal[i-1]);
          break;
        }
      }
      return Count;
    }
    
    /// countLeadingZeros - This function is an APInt version of the
    /// countLeadingZeros_{32,64} functions in MathExtras.h. It counts the number
    /// of zeros from the most significant bit to the first one bit.
    /// @returns BitWidth if the value is zero.
    /// @returns the number of zeros from the most significant bit to the first
    /// one bits.
    unsigned countLeadingZeros() const {
      if (isSingleWord()) {
        unsigned unusedBits = APINT_BITS_PER_WORD - BitWidth;
        return CountLeadingZeros_64(VAL) - unusedBits;
      }
      return countLeadingZerosSlowCase();
    }
    
    /// This function returns the number of active bits which is defined as the
    /// bit width minus the number of leading zeros. This is used in several
    /// computations to see how "wide" the value is.
    /// @brief Compute the number of active bits in the value
    unsigned getActiveBits() const {
      return BitWidth - countLeadingZeros();
    }
    
    /// This method attempts to return the value of this APInt as a zero extended
    /// uint64_t. The bitwidth must be <= 64 or the value must fit within a
    /// uint64_t. Otherwise an assertion will result.
    /// @brief Get zero extended value
    uint64_t getZExtValue() const {
      if (isSingleWord())
        return VAL;
      assert(getActiveBits() <= 64 && "Too many bits for uint64_t");
      return pVal[0];
    }
    
    /// getLimitedValue - If this value is smaller than the specified limit,
    /// return it, otherwise return the limit value.  This causes the value
    /// to saturate to the limit.
    uint64_t getLimitedValue(uint64_t Limit = ~0ULL) const {
      return (getActiveBits() > 64 || getZExtValue() > Limit) ?
          Limit :  getZExtValue();
    }
    
    /// This function returns a pointer to the internal storage of the APInt.
    /// This is useful for writing out the APInt in binary form without any
    /// conversions.
    const uint64_t* getRawData() const {
      if (isSingleWord())
        return &VAL;
      return &pVal[0];
    }
    
    /// @}
    /// @name Resizing Operators
    /// @{
    /// Truncate the APInt to a specified width. It is an error to specify a width
    /// that is greater than or equal to the current width.
    /// @brief Truncate to new width.
    APIntLite trunc(unsigned width) const {
      assert(width < BitWidth && "Invalid APInt Truncate request");
      assert(width && "Can't truncate to 0 bits");

      if (width <= APINT_BITS_PER_WORD)
        return APIntLite(width, getRawData()[0]);

      APIntLite Result(getMemory(getNumWords(width)), width);

      // Copy full words.
      unsigned i;
      for (i = 0; i != width / APINT_BITS_PER_WORD; i++)
        Result.pVal[i] = pVal[i];

      // Truncate and copy any partial word.
      unsigned bits = (0 - width) % APINT_BITS_PER_WORD;
      if (bits != 0)
        Result.pVal[i] = pVal[i] << bits >> bits;

      return Result;
    }
    
    /// This operation zero extends the APInt to a new width. The high order bits
    /// are filled with 0 bits.  It is an error to specify a width that is less
    /// than or equal to the current width.
    /// @brief Zero extend to a new width.
    APIntLite zext(unsigned width) const {
      assert(width > BitWidth && "Invalid APInt ZeroExtend request");
      
      if (width <= APINT_BITS_PER_WORD)
        return APIntLite(width, VAL);
      
      APIntLite Result(getMemory(getNumWords(width)), width);
      
      // Copy words.
      unsigned i;
      for (i = 0; i != getNumWords(); i++)
        Result.pVal[i] = getRawData()[i];
      
      // Zero remaining words.
      memset(&Result.pVal[i], 0, (Result.getNumWords() - i) * APINT_WORD_SIZE);
      
      return Result;
    }
    
    /// Make this APInt have the bit width given by \p width. The value is zero
    /// extended, truncated, or left alone to make it that width.
    /// @brief Zero extend or truncate to width
    APIntLite zextOrTrunc(unsigned width) const {
      if (BitWidth < width)
        return zext(width);
      if (BitWidth > width)
        return trunc(width);
      return *this;
    }
    
    /// Arithmetic right-shift this APInt by shiftAmt.
    /// @brief Arithmetic right-shift function.
    APIntLite ashr(unsigned shiftAmt) const {
      assert(shiftAmt <= BitWidth && "Invalid shift amount");
      // Handle a degenerate case
      if (shiftAmt == 0)
        return *this;

      // Handle single word shifts with built-in ashr
      if (isSingleWord()) {
        if (shiftAmt == BitWidth)
          return APIntLite(BitWidth, 0); // undefined
        else {
          unsigned SignBit = APINT_BITS_PER_WORD - BitWidth;
          return APIntLite(BitWidth,
            (((int64_t(VAL) << SignBit) >> SignBit) >> shiftAmt));
        }
      }

      // If all the bits were shifted out, the result is, technically, undefined.
      // We return -1 if it was negative, 0 otherwise. We check this early to avoid
      // issues in the algorithm below.
      if (shiftAmt == BitWidth) {
        if (isNegative())
          return APIntLite(BitWidth, -1ULL, true);
        else
          return APIntLite(BitWidth, 0);
      }

      // Create some space for the result.
      uint64_t * val = new uint64_t[getNumWords()];

      // Compute some values needed by the following shift algorithms
      unsigned wordShift = shiftAmt % APINT_BITS_PER_WORD; // bits to shift per word
      unsigned offset = shiftAmt / APINT_BITS_PER_WORD; // word offset for shift
      unsigned breakWord = getNumWords() - 1 - offset; // last word affected
      unsigned bitsInWord = whichBit(BitWidth); // how many bits in last word?
      if (bitsInWord == 0)
        bitsInWord = APINT_BITS_PER_WORD;

      // If we are shifting whole words, just move whole words
      if (wordShift == 0) {
        // Move the words containing significant bits
        for (unsigned i = 0; i <= breakWord; ++i)
          val[i] = pVal[i+offset]; // move whole word

        // Adjust the top significant word for sign bit fill, if negative
        if (isNegative())
          if (bitsInWord < APINT_BITS_PER_WORD)
            val[breakWord] |= ~0ULL << bitsInWord; // set high bits
      } else {
        // Shift the low order words
        for (unsigned i = 0; i < breakWord; ++i) {
          // This combines the shifted corresponding word with the low bits from
          // the next word (shifted into this word's high bits).
          val[i] = (pVal[i+offset] >> wordShift) |
                   (pVal[i+offset+1] << (APINT_BITS_PER_WORD - wordShift));
        }

        // Shift the break word. In this case there are no bits from the next word
        // to include in this word.
        val[breakWord] = pVal[breakWord+offset] >> wordShift;

        // Deal with sign extenstion in the break word, and possibly the word before
        // it.
        if (isNegative()) {
          if (wordShift > bitsInWord) {
            if (breakWord > 0)
              val[breakWord-1] |=
                ~0ULL << (APINT_BITS_PER_WORD - (wordShift - bitsInWord));
            val[breakWord] |= ~0ULL;
          } else
            val[breakWord] |= (~0ULL << (bitsInWord - wordShift));
        }
      }

      // Remaining words are 0 or -1, just assign them.
      uint64_t fillValue = (isNegative() ? -1ULL : 0);
      for (unsigned i = breakWord+1; i < getNumWords(); ++i)
        val[i] = fillValue;
      return APIntLite(val, BitWidth).clearUnusedBits();
    }
};

}

#endif
