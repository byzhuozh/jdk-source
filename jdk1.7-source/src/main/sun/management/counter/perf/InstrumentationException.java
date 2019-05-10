/*
 * Copyright (c) 2003, Oracle and/or its affiliates. All rights reserved.
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

package sun.management.counter.perf;

public class InstrumentationException extends RuntimeException {
    /**
     * Constructs a <tt>InstrumentationException</tt> with no
     * detail mesage.
     */
     public InstrumentationException() {
     }

    /**
     * Constructs a <tt>InstrumentationException</tt> with a specified
     * detail mesage.
     *
     * @param message the detail message
     */
     public InstrumentationException(String message) {
         super(message);
     }

     private static final long serialVersionUID = 8060117844393922797L;
}
