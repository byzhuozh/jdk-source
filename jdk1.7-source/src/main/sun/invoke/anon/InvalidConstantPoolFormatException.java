/*
 * Copyright (c) 2008, 2011, Oracle and/or its affiliates. All rights reserved.
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

package sun.invoke.anon;

/** Exception used when there is an error in the constant pool
 *  format.
 */
public class InvalidConstantPoolFormatException extends Exception {
    private static final long serialVersionUID=-6103888330523770949L;

    public InvalidConstantPoolFormatException(String message,Throwable cause) {
        super(message,cause);
    }

    public InvalidConstantPoolFormatException(String message) {
        super(message);
    }

    public InvalidConstantPoolFormatException(Throwable cause) {
        super(cause);
    }
}
