/*
 * Copyright (c) 1997, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */
package sun.io;

import sun.nio.cs.ext.DoubleByte;
import static sun.nio.cs.CharsetMapping.*;

public abstract class ByteToCharDBCS_ASCII extends ByteToCharConverter
{
    private boolean savedBytePresent;
    private int savedByte;

    private DoubleByte.Decoder dec;

    public ByteToCharDBCS_ASCII(DoubleByte.Decoder dec) {
        super();
        savedBytePresent = false;
        this.dec = dec;
    }

    char decodeSingle(int b) {
        return dec.decodeSingle(b);
    }

    char decodeDouble(int b1, int b2) {
        return dec.decodeDouble(b1, b2);
    }

    public int flush(char [] output, int outStart, int outEnd)
        throws MalformedInputException
    {

       if (savedBytePresent) {
           reset();
           badInputLength = 0;
           throw new MalformedInputException();
       }

       reset();
       return 0;
    }

    /**
     * Character conversion
     */
    public int convert(byte[] input, int inOff, int inEnd,
                       char[] output, int outOff, int outEnd)
        throws UnknownCharacterException, MalformedInputException,
               ConversionBufferFullException
    {
        int inputSize;
        char    outputChar = UNMAPPABLE_DECODING;

        charOff = outOff;
        byteOff = inOff;

        while(byteOff < inEnd)
        {
           int byte1;

           if (!savedBytePresent) {
              byte1 = input[byteOff] & 0xff;
              inputSize = 1;
           } else {
              byte1 = savedByte;
              savedBytePresent = false;
              inputSize = 0;
           }

           outputChar = decodeSingle(byte1);
           if (outputChar == UNMAPPABLE_DECODING) {

              if (byteOff + inputSize >= inEnd) {
                savedByte = byte1;
                savedBytePresent = true;
                byteOff += inputSize;
                break;
              }

              outputChar = decodeDouble(byte1, input[byteOff+inputSize] & 0xff);
              inputSize++;
           }

           if (outputChar == UNMAPPABLE_DECODING) {
              if (subMode)
                 outputChar = subChars[0];
              else {
                 badInputLength = inputSize;
                 throw new UnknownCharacterException();
              }
           }

           if (charOff >= outEnd)
              throw new ConversionBufferFullException();

           output[charOff++] = outputChar;
           byteOff += inputSize;

        }

        return charOff - outOff;
    }

    /**
     *  Resets the converter.
     */
    public void reset() {
       charOff = byteOff = 0;
       savedBytePresent = false;
    }
}
