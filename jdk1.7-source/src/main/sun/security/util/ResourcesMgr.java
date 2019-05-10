/*
 * Copyright (c) 2000, 2006, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.util;

/**
 */
public class ResourcesMgr {

    // intended for java.security, javax.security and sun.security resources
    private static java.util.ResourceBundle bundle;

    // intended for com.sun.security resources
    private static java.util.ResourceBundle altBundle;

    public static String getString(String s) {

        if (bundle == null) {

            // only load if/when needed
            bundle = java.security.AccessController.doPrivileged(
                new java.security.PrivilegedAction<java.util.ResourceBundle>() {
                public java.util.ResourceBundle run() {
                    return (java.util.ResourceBundle.getBundle
                                ("sun.security.util.Resources"));
                }
            });
        }

        return bundle.getString(s);
    }

    public static String getString(String s, final String altBundleName) {

        if (altBundle == null) {

            // only load if/when needed
            altBundle = java.security.AccessController.doPrivileged(
                new java.security.PrivilegedAction<java.util.ResourceBundle>() {
                public java.util.ResourceBundle run() {
                    return (java.util.ResourceBundle.getBundle(altBundleName));
                }
            });
        }

        return altBundle.getString(s);
    }
}
