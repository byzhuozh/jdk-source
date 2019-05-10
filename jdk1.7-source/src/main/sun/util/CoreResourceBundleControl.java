/*
 * Copyright (c) 2005, Oracle and/or its affiliates. All rights reserved.
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



package sun.util;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.ResourceBundle;
import java.util.ResourceBundle.Control;

/**
 * This is a convenient class for loading some of internal resources faster
 * if they are built with Resources.gmk defined in J2SE workspace. Also,
 * they have to be in class file format.
 *
 * "LOCALE_LIST" will be replaced at built time by a list of locales we
 * defined in Defs.gmk. We want to exclude these locales from search to
 * gain better performance. For example, since we know if the resource
 * is built with Resources.gmk, they are not going to provide basename_en.class
 * & basename_en_US.class resources, in that case, continuing searching them
 * is expensive. By excluding them from the candidate locale list, these
 * resources won't be searched.
 *
 * @since 1.6.
 */
public class CoreResourceBundleControl extends ResourceBundle.Control {
    /* the candidate locale list to search */
    private final Collection<Locale> excludedJDKLocales;
    /* singlton instance of the resource bundle control. */
    private static CoreResourceBundleControl resourceBundleControlInstance =
        new CoreResourceBundleControl();

    protected CoreResourceBundleControl() {
        excludedJDKLocales = Arrays.asList(Locale.GERMANY, Locale.ENGLISH, Locale.US, new Locale("es", "ES"), Locale.FRANCE, Locale.ITALY, Locale.JAPAN, Locale.KOREA, new Locale("sv", "SE"), Locale.CHINESE);
    }

    /**
     * This method is to provide a customized ResourceBundle.Control to speed
     * up the search of resources in JDK.
     *
     * @return the instance of resource bundle control.
     */
    public static CoreResourceBundleControl getRBControlInstance() {
        return resourceBundleControlInstance;
    }

    /**
     * This method is to provide a customized ResourceBundle.Control to speed
     * up the search of resources in JDK, with the bundle's package name check.
     *
     * @param bundleName bundle name to check
     * @return the instance of resource bundle control if the bundle is JDK's,
     *    otherwise returns null.
     */
    public static CoreResourceBundleControl getRBControlInstance(String bundleName) {
        if (bundleName.startsWith("com.sun.") ||
            bundleName.startsWith("java.") ||
            bundleName.startsWith("javax.") ||
            bundleName.startsWith("sun.")) {
            return resourceBundleControlInstance;
        } else {
            return null;
        }
    }

    /**
     * @returns a list of candidate locales to search from.
     * @exception NullPointerException if baseName or locale is null.
     */
    @Override
    public List<Locale> getCandidateLocales(String baseName, Locale locale) {
        List<Locale> candidates = super.getCandidateLocales(baseName, locale);
        candidates.removeAll(excludedJDKLocales);
        return candidates;
    }

    /**
     * @ returns TTL_DONT_CACHE so that ResourceBundle instance won't be cached.
     * User of this CoreResourceBundleControl should probably maintain a hard reference
     * to the ResourceBundle object themselves.
     */
    @Override
    public long getTimeToLive(String baseName, Locale locale) {
        return ResourceBundle.Control.TTL_DONT_CACHE;
    }
}
