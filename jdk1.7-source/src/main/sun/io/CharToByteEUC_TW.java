/*
 * Copyright (c) 1996, 2003, Oracle and/or its affiliates. All rights reserved.
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

import sun.nio.cs.ext.EUC_TW;

/*
 * @author Limin Shi
 */

public class CharToByteEUC_TW extends CharToByteConverter
{
    private final EUC_TW.Encoder enc = (EUC_TW.Encoder)(new EUC_TW().newEncoder());

    public int flush(byte[] output, int outStart, int outEnd)
        throws MalformedInputException
    {
        reset();
        return 0;
    }

    public void reset() {
        byteOff = charOff = 0;
    }

    public boolean canConvert(char ch){
        return enc.canEncode(ch);
    }

    /**
     * Character conversion
     */
    public int convert(char[] input, int inOff, int inEnd,
                       byte[] output, int outOff, int outEnd)
        throws UnknownCharacterException, MalformedInputException,
               ConversionBufferFullException
    {
        int outputSize;
        byte [] tmpbuf = new byte[4];;
        byte [] outputByte;
        byteOff = outOff;

        //Fixed 4122961 by bringing the charOff++ out to this
        // loop where it belongs, changing the loop from
        // while(){} to for(){}.
        for (charOff = inOff; charOff < inEnd; charOff++) {
            outputByte = tmpbuf;
            if ( input[charOff] < 0x80) {       // ASCII
                outputSize = 1;
                outputByte[0] = (byte)(input[charOff] & 0x7f);
            } else {
                outputSize = enc.toEUC(input[charOff], outputByte);
            }

            if (outputSize == -1) {
                if (subMode) {
                    outputByte = subBytes;
                    outputSize = subBytes.length;
                } else {
                    badInputLength = 1;
                    throw new UnknownCharacterException();
                }
            }

            if (outEnd - byteOff < outputSize)
                throw new ConversionBufferFullException();

            for (int i = 0; i < outputSize; i++)
                output[byteOff++] = outputByte[i];
        }

        return byteOff - outOff;

    }

    /**
     * returns the maximum number of bytes needed to convert a char
     */
    public int getMaxBytesPerChar() {
        return 4;
    }

    /**
     * Return the character set ID
     */
    public String getCharacterEncoding() {
        return "EUC_TW";
    }
}
