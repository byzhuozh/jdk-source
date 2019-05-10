/*
 * Copyright (c) 2009, Oracle and/or its affiliates. All rights reserved.
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

package sun.swing;

import sun.misc.Unsafe;

import java.awt.Point;

import javax.swing.text.JTextComponent;
import javax.swing.TransferHandler;

/**
 * The SwingAccessor utility class.
 * The main purpose of this class is to enable accessing
 * private and package-private fields of classes from
 * different classes/packages. See sun.misc.SharedSecretes
 * for another example.
 */
public final class SwingAccessor {
    private static final Unsafe unsafe = Unsafe.getUnsafe();

    /**
     * We don't need any objects of this class.
     * It's rather a collection of static methods
     * and interfaces.
     */
    private SwingAccessor() {
    }

    /**
     * An accessor for the JTextComponent class.
     * Note that we intentionally introduce the JTextComponentAccessor,
     * and not the JComponentAccessor because the needed methods
     * aren't override methods.
     */
    public interface JTextComponentAccessor {

        /**
         * Calculates a custom drop location for the text component,
         * representing where a drop at the given point should insert data.
         */
        TransferHandler.DropLocation dropLocationForPoint(JTextComponent textComp, Point p);

        /**
         * Called to set or clear the drop location during a DnD operation.
         */
        Object setDropLocation(JTextComponent textComp, TransferHandler.DropLocation location,
                               Object state, boolean forDrop);
    }

    /**
     * The javax.swing.text.JTextComponent class accessor object.
     */
    private static JTextComponentAccessor jtextComponentAccessor;

    /**
     * Set an accessor object for the javax.swing.text.JTextComponent class.
     */
    public static void setJTextComponentAccessor(JTextComponentAccessor jtca) {
         jtextComponentAccessor = jtca;
    }

    /**
     * Retrieve the accessor object for the javax.swing.text.JTextComponent class.
     */
    public static JTextComponentAccessor getJTextComponentAccessor() {
        if (jtextComponentAccessor == null) {
            unsafe.ensureClassInitialized(JTextComponent.class);
        }

        return jtextComponentAccessor;
    }
}
