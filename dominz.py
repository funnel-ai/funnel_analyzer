"""
Streamlit Sales Funnel Structure Analyzer v3.0 - Elite Edition
Advanced discovery techniques for finding linked and potentially unlinked funnel pages.
"""

import asyncio
import csv
import io
import logging
import os
import pandas as pd
import random
import re
import streamlit as st
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field, replace as dataclasses_replace
from enum import Enum, auto
from pathlib import Path
from typing import (Any, AsyncGenerator, Dict, List, Optional, Set, Tuple,
                    Union, FrozenSet, Callable)
from urllib.parse import urljoin, urlparse, parse_qs, urlunparse
from xml.etree import ElementTree as ET # For Sitemap Parsing

# Third-party imports
import aiohttp
import tldextract
from bs4 import BeautifulSoup, SoupStrainer
try:
    # Try importing Pydantic V2 components first
    from pydantic import BaseModel, HttpUrl, ValidationError, Field, field_validator, AnyHttpUrl
    PYDANTIC_V2 = True
except ImportError:
    # Fallback to Pydantic V1 if V2 is not available
    from pydantic import BaseModel, HttpUrl, ValidationError, Field, validator
    PYDANTIC_V2 = False
    # Alias AnyHttpUrl to HttpUrl for compatibility in V1 context
    AnyHttpUrl = HttpUrl
from urllib.robotparser import RobotFileParser

# Try importing lxml for faster parsing
try:
    import lxml
    DEFAULT_PARSER = "lxml"
except ImportError:
    DEFAULT_PARSER = "html.parser"
    # Display warning only once using session state
    if 'lxml_warning_shown' not in st.session_state:
        st.sidebar.warning("`lxml` not found. Using Python's built-in HTML parser (might be slower). Install with `pip install lxml` for potential speed improvements.", icon="⚠️")
        st.session_state.lxml_warning_shown = True


# --- Logging Configuration ---
log_formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
log_stream_handler = logging.StreamHandler() # Log to console/Streamlit log
log_stream_handler.setFormatter(log_formatter)
# Optional File Logging (consider permissions in deployed environments)
log_file_path = Path("./funnel_analyzer_elite.log") # Log in app directory
try:
    log_file_handler = logging.FileHandler(log_file_path, mode='a', encoding='utf-8')
    log_file_handler.setFormatter(log_formatter)
except (PermissionError, OSError) as log_err: # Catch OSError too for path issues
     st.sidebar.error(f"Failed to create log file ({log_file_path}): {log_err}", icon="🔥")
     log_file_handler = None

handlers_list = [log_stream_handler]
if log_file_handler:
     handlers_list.append(log_file_handler)

# Configure root logger
logging.basicConfig(
    level=logging.INFO, # Default level, can be changed via UI
    handlers=handlers_list,
    force=True # Force reconfiguration in case Streamlit messes with logging
)
logger = logging.getLogger("funnel_analyzer_elite")
# Silence noisy libraries if needed
logging.getLogger("aiohttp").setLevel(logging.WARNING)
logging.getLogger("asyncio").setLevel(logging.WARNING)
# --------------------------------------------------------------

# --- Constants ---
# Common keywords for URL guessing (expandable)
COMMON_FUNNEL_KEYWORDS = [
    'thank-you', 'thanks', 'oto', 'upsell', 'downsell', 'special-offer',
    'order-confirmation', 'receipt', 'checkout', 'cart', 'payment', 'billing',
    'members', 'login', 'dashboard', 'account', 'portal', 'webinar', 'register',
    'optin', 'subscribe', 'freebie', 'download', 'access', 'confirmation',
    'upgrade', 'onetimeoffer', 'step2', 'next-step', 'bonus', 'exclusive',
    # Add more variations if needed
    'thankyou', 'order', 'special', 'member', 'webinar-registration', 'oto1', 'oto2', 'upsell1', 'upsell2'
]
COMMON_EXTENSIONS = ['', '.html', '.php', '.aspx', '.jsp'] # Common extensions to guess

# Regex to find potential paths/URLs in JavaScript (can be improved)
# Looks for strings starting with / or word/, excluding //, and not containing excessive ../
# Adjusted to better handle paths and optional extensions
JS_URL_REGEX = re.compile(r'["\']((?:/[^/"\'\s?#*<>|:]+|(?:\w+/)[^/"\'\s?#*<>|:]+)(?:\.(?:html|php|aspx?|jpsx?))?)["\']', re.IGNORECASE)
# -----------------


# --- Core Class Definitions ---

class PageClassificationType(Enum):
    """Enumeration for page classification types for enhanced type safety."""
    THANK_YOU = auto()
    UPSELL = auto()
    DOWNSELL = auto()
    CHECKOUT = auto()
    LEAD_CAPTURE = auto()
    WEBINAR = auto()
    MEMBERS_AREA = auto()
    HIDDEN_BY_URL = auto()          # Explicitly marked as hidden in URL/Content
    POTENTIAL_HIDDEN = auto()    # Inferred by low link count
    UNKNOWN = auto()
    ERROR = auto()                 # Page resulted in an error during fetch/parse

    # Meta-classifications (derived from content, not just URL)
    CONTENT_THANK_YOU = auto()
    CONTENT_UPSELL = auto()
    CONTENT_DOWNSELL = auto()
    CONTENT_CHECKOUT = auto()
    CONTENT_LEAD_CAPTURE = auto()
    CONTENT_WEBINAR = auto()
    CONTENT_MEMBERS_AREA = auto()

    # Additional derived classifications (might overlap or refine others)
    ORDER_CONFIRMATION = auto() # More specific than THANK_YOU
    RECEIPT = auto()            # More specific than THANK_YOU
    ORDER_FORM = auto()         # Potentially distinct from CHECKOUT

    def __str__(self):
        # Make names more readable
        return self.name.replace('_', ' ').title()


class PagePatterns(BaseModel):
    """Configuration model for page classification patterns (Regex)."""
    # Using raw strings (r'') for all regex patterns is good practice
    thank_you: List[str] = Field(default=[
        r'thank[-_]?you', r'\bthanks\b', r'confirmation', r'success',
        r'order[-_]?complete', r'purchase[-_]?complete', r'receipt', r'order[-_]?received'
    ])
    upsell: List[str] = Field(default=[
        r'upsell', r'upgrade', r'special[-_]?offer', r'one[-_]?time[-_]?offer',
        r'\boto\d?\b', r'/oto\b', r'bump', r'addons?', r'add[-_]?ons?', r'cross[-_]?sell',
        r'next[-_]?step', r'continue' # Sometimes used on upsell pages
    ])
    downsell: List[str] = Field(default=[
        r'downsell', r'down[-_]?sell', r'alternative[-_]?offer', r'discount[-_]?offer',
        r'special[-_]?discount', r'second[-_]?chance', r'no[-_]?thanks' # Often in downsell URL paths
    ])
    checkout: List[str] = Field(default=[
        r'checkout', r'payment', r'billing', r'order[-_]?form', r'\bcart\b',
        r'secure[-_]?checkout', r'purchase', r'buy[-_]?now', r'complete[-_]?order',
        r'submit[-_]?order'
    ])
    lead_capture: List[str] = Field(default=[
        r'opt[-_]?in', r'subscribe', r'sign[-_]?up', r'register', r'join',
        r'lead[-_]?magnet', r'free[-_]?(?:book|guide|report|webinar|training|download|gift|trial)'
    ])
    webinar: List[str] = Field(default=[
        r'webinar', r'training', r'workshop', r'masterclass', r'\bclass\b',
        r'live[-_]?event', r'registration', r'webcast'
    ])
    members_area: List[str] = Field(default=[
        r'members?', r'login', r'dashboard', r'account', r'portal',
        r'my[-_]?account', r'customer[-_]?area', r'signin'
    ])
    hidden_indicators: List[str] = Field(default=[
        r'private', r'secret', r'hidden', r'exclusive', r'vip', r'internal',
        r'unlisted', r'restricted', r'unpublished', r'preview', r'backdoor'
    ])
    # Simplified content keywords for initial check
    payment_form_indicators: List[str] = Field(default=[
        'credit card', 'card number', 'expiration date', 'cvv', 'cvc',
        'billing address', 'payment information', 'secure payment', 'stripe', 'paypal', # Common providers
        'zip code', 'postal code' # Often near payment fields
    ])
    price_patterns: List[str] = Field(default=[
        r'\$\s?\d+(?:[,.]\d{2,3})*(?:\.\d{2})?',  # $XX,XXX.XX or $XX.XXX,XX
        r'\d+\s*(?:dollars|usd|eur|gbp|cad|aud)\b', # XX dollars/usd/eur/gbp etc.
        r'\b(?:price|cost|fee|total|amount)\s*[:=\-]?\s*\$?\s?\d+', # price: $XX
        r'\b(?:add to cart|buy now|purchase|order now|checkout|get access|enroll)\b' # buttons often imply pricing nearby (case-insensitive)
    ])


# ***** CrawlerConfig defined AFTER PagePatterns *****
class CrawlerConfig(BaseModel):
    """Configuration for the web crawler."""
    start_url: AnyHttpUrl # Use AnyHttpUrl for slightly more flexible input
    manual_urls: List[AnyHttpUrl] = Field(default_factory=list)
    max_pages: int = Field(default=500, gt=0)
    user_agent: str = Field(default="SalesFunnelAnalyzer-Elite/3.0 (+https://github.com/your-repo-here)") # Add a real link if possible
    request_delay: float = Field(default=1.0, ge=0)
    request_delay_jitter: float = Field(default=0.5, ge=0)
    timeout: float = Field(default=20.0, gt=0)
    respect_robots_txt: bool = True
    max_retries: int = Field(default=2, ge=0) # Slightly reduced default
    concurrent_requests: int = Field(default=5, gt=0)
    max_redirects: int = Field(default=10, ge=0) # Increased default
    page_patterns: PagePatterns = Field(default_factory=PagePatterns)

    # --- New Discovery Options ---
    find_sitemaps: bool = True
    attempt_url_guessing: bool = False
    analyze_javascript: bool = False
    max_guessed_urls_per_page: int = Field(default=10, ge=0) # Limit noise

    # Helper method to ensure URL scheme (used by validators)
    @classmethod
    def _ensure_scheme(cls, url_str: str) -> str:
        """Adds http:// scheme if missing."""
        if isinstance(url_str, str):
            url_str = url_str.strip()
            if not url_str:
                raise ValueError("URL cannot be empty")
            # Simple check if scheme exists
            if "://" not in url_str:
                # Default to https for security
                logger.debug(f"Adding https:// scheme to URL: {url_str}")
                return 'https://' + url_str
            # Check if scheme is http/https (allow others like ftp? maybe not needed)
            if not url_str.lower().startswith(('http://', 'https://')):
                 # Raise error for unsupported schemes if AnyHttpUrl validation won't catch it
                 logger.warning(f"URL scheme is not http or https: {url_str}. Validation might fail.")
                 # Or raise ValueError('URL scheme must be http or https')
        return url_str # Return original if not string or already valid/handled

    # Pydantic v1/v2 compatibility for validation
    if PYDANTIC_V2:
        # Pydantic V2: Use field_validator
        # It's often clearer to have separate validators per field
        @field_validator('start_url', mode='before')
        @classmethod
        def validate_single_start_url_v2(cls, v):
            # Logic specifically for start_url
            return cls._ensure_scheme(v)

        @field_validator('manual_urls', mode='before')
        @classmethod
        def validate_manual_urls_v2(cls, v):
            # Logic specifically for manual_urls list
            if isinstance(v, list):
                return [cls._ensure_scheme(url) for url in v if isinstance(url, str)]
            # Handle case where a single string might be passed mistakenly for manual_urls
            elif isinstance(v, str):
                 logger.warning("Manual URLs received a single string, wrapping in list.")
                 return [cls._ensure_scheme(v)]
            return v # Pass through other types

    else:
        # Pydantic V1: Use validator (with correct indentation)
        @validator('start_url', pre=True, allow_reuse=True) # allow_reuse might be needed if name reused (though using different names is better)
        @classmethod
        def validate_single_start_url_v1(cls, v):
            """Validator for the single start_url field (Pydantic V1)."""
            # logger.debug(f"Validating start_url (V1): {v}") # Optional debug log
            return cls._ensure_scheme(v)

        @validator('manual_urls', pre=True, each_item=True, allow_reuse=True) # allow_reuse might be needed if name reused
        @classmethod
        def validate_each_manual_url_item_v1(cls, v):
            """Validator for each item in the manual_urls list (Pydantic V1)."""
            # logger.debug(f"Validating manual_url item (V1): {v}") # Optional debug log
            # Since each_item=True, v is already a single item from the list
            return cls._ensure_scheme(v)


# --- Dataclasses for storing page information ---
# (Keep the rest of your code below this point)
# ... (Your existing dataclasses like PageInfo, CrawlResult, etc.) ...
# ... (Your existing functions like fetch, parse_links, classify_page, etc.) ...
# ... (Your Streamlit UI code) ...
        def validate_urls_v1(cls, v):
            if isinstance(v, str):
                return cls._ensure_scheme(v)
            return v # Pass through if not a string

    @staticmethod
    def _ensure_scheme(url_str: str) -> str:
        """Adds http:// scheme if missing."""
        url_str = url_str.strip()
        if not url_str:
            raise ValueError("URL cannot be empty")
        if "://" not in url_str:
            # Don't log warning here, do it later if needed
            return 'http://' + url_str
        # Check if scheme is http/https, allow others through for now, let AnyHttpUrl validate fully
        if not url_str.lower().startswith(('http://', 'https://')):
             # Maybe raise error or log warning? For now, allow AnyHttpUrl to handle it.
             pass
        return url_str

    # Store domain info as instance variable, not model field
    _domain_info_cache: Optional[Dict[str, str]] = None

    # Use a method to get domain info, calculating only once
    def get_domain_info(self) -> Dict[str, str]:
        """Extract domain information from the start URL (cached)."""
        if self._domain_info_cache is None:
            try:
                # Use the validated start_url which should have a scheme
                url_str = str(self.start_url)
                parsed_start = urlparse(url_str)
                extracted = tldextract.extract(url_str)
                netloc_lower = parsed_start.netloc.lower()
                registered_domain = extracted.registered_domain.lower()

                if not registered_domain:
                    # Handle cases like IP addresses or localhost
                    logger.warning(f"Could not extract registered domain from {url_str}. Crawling will be restricted to exact hostname: {netloc_lower}")
                    registered_domain = netloc_lower # Fallback to netloc

                self._domain_info_cache = {
                    "registered_domain": registered_domain,
                    "subdomain": extracted.subdomain.lower(),
                    "domain": extracted.domain.lower(),
                    "suffix": extracted.suffix.lower(),
                    "netloc": netloc_lower, # Store the specific netloc of the start URL
                    "scheme": parsed_start.scheme.lower()
                }
            except Exception as e:
                logger.exception(f"Error extracting domain info from {self.start_url}: {e}")
                # Provide a minimal fallback to prevent crashes, though crawling might fail
                self._domain_info_cache = {
                    "registered_domain": urlparse(str(self.start_url)).netloc.lower(),
                    "subdomain": "", "domain": "", "suffix": "",
                    "netloc": urlparse(str(self.start_url)).netloc.lower(),
                    "scheme": urlparse(str(self.start_url)).scheme.lower() or "http"
                }
        return self._domain_info_cache


@dataclass(frozen=True)
class PageData:
    """Data structure for storing processed page information."""
    url: str                       # Original URL requested (might differ from key)
    final_url: str                 # URL after redirects
    crawl_key: str                 # Canonical key used for visited/data storage
    status_code: int
    content_type: Optional[str] = None
    title: Optional[str] = "No Title Found"
    classifications: FrozenSet[PageClassificationType] = field(default_factory=frozenset)
    content_length: Optional[int] = None
    has_forms: bool = False
    form_count: int = 0
    has_payment_indicators: bool = False # Changed name for clarity
    has_pricing_indicators: bool = False # Changed name for clarity
    prices_found: Tuple[str, ...] = field(default_factory=tuple)
    redirect_history: Tuple[str, ...] = field(default_factory=tuple)
    error_message: Optional[str] = None
    crawl_timestamp: float = field(default_factory=time.time)
    discovery_method: str = "Unknown"


class UrlUtils:
    """Utility methods for URL handling and normalization."""
    # Expanded list of common tracking parameters
    _TRACKING_PARAMS: Set[str] = {
        # Google Analytics
        'utm_source', 'utm_medium', 'utm_campaign', 'utm_term', 'utm_content',
        'utm_id', 'utm_source_platform', 'utm_creative_format', 'utm_marketing_tactic',
        '_ga', '_gl', 'gclid', 'dclid',
        # Facebook/Meta
        'fbclid', '_fbc', '_fbp',
        # Microsoft/Bing
        'msclkid',
        # Yahoo/Verizon
        'yclid',
        # Mailchimp
        'mc_eid', 'mc_cid',
        # HubSpot
        '_hsenc', '_hsmi', '__hssc', '__hstc', 'hsCtaTracking',
        # Adobe Analytics / Omniture
        's_kwcid', 'ef_id', 's_cid',
        # Other Common Affiliate/Tracking
        'affiliate_id', 'aff_id', 'aff', 'tracker', 'tracking_id', 'trafficsource',
        'campaign_id', 'adgroupid', 'adid', 'keyword', 'matchtype', 'device',
        'ref', 'source', 'referrer', 'origin', 'medium',
        'pk_campaign', 'pk_kwd', 'pk_source', 'pk_medium', 'pk_content', # Matomo/Piwik
        'piwik_campaign', 'piwik_kwd', 'piwik_keyword',
        'cjevent', # Commission Junction
        'zanpid', # Zanox/Awin
        'widgetid', # Outbrain/Taboola often use this
        'gclsrc', # Google Click Source
        'wbraid', # Google Ads Web to App/Cross-Device
        'gbraid', # Google Ads App to Web/Cross-Device
    }
    _NORMALIZE_SCHEMES = {'http', 'https'} # Only normalize these

    @classmethod
    def is_tracking_param(cls, param_name: str) -> bool:
        param_lower = param_name.lower()
        # Check prefix first for efficiency
        if param_lower.startswith(('utm_', 'pk_', 'piwik_', '_', 'mc_', 'hs', 's_', '__')):
            return True
        return param_lower in cls._TRACKING_PARAMS

    @classmethod
    def get_crawl_key(cls, url: str) -> str:
        """Generates a normalized URL key for tracking visited/processed pages."""
        try:
            # Ensure basic validity and scheme before heavy processing
            if not url or "://" not in url:
                # Cannot generate a reliable key without a scheme and netloc
                # This should ideally be handled before calling get_crawl_key
                logger.warning(f"Cannot generate key for URL without scheme: {url}")
                return url # Return original as fallback

            parsed = urlparse(url)

            # Only normalize http/https schemes, leave others (like mailto, data) alone if passed mistakenly
            scheme = parsed.scheme.lower() if parsed.scheme else 'http' # Should have scheme by now
            if scheme not in cls._NORMALIZE_SCHEMES:
                return url # Don't normalize non-web URLs

            netloc = parsed.netloc.lower()
            if not netloc: # Should not happen if '://' is present, but be safe
                 return url

            # Normalize path: remove trailing slash, ensure leading slash
            path = parsed.path
            if len(path) > 1 and path.endswith('/'):
                 path = path[:-1]
            elif not path:
                 path = '/'

            # Normalize query parameters: remove tracking, sort remaining
            query_params = parse_qs(parsed.query, keep_blank_values=True)
            meaningful_params = {}
            for k, v in query_params.items():
                if not cls.is_tracking_param(k):
                    # Sort values within each parameter key for consistency
                    meaningful_params[k] = sorted(v)

            # Sort parameter keys and rebuild query string
            sorted_keys = sorted(meaningful_params.keys())
            query_parts = []
            for k in sorted_keys:
                # Join multiple values with comma (consistent approach)
                query_parts.append(f"{k}={','.join(meaningful_params[k])}")
            query = "&".join(query_parts)

            # Ignore fragment (#...)
            return urlunparse((scheme, netloc, path, '', query, ''))

        except ValueError as e:
            logger.error(f"Could not parse URL for key generation: {url} - Error: {e}")
            return url # Fallback to original URL if parsing fails

    @classmethod
    def is_within_scope(cls, url: str, target_domain_info: Dict[str, str]) -> bool:
        """Checks if a URL belongs to the same registered domain or exact hostname (if no registered domain)."""
        try:
            # Ensure URL has scheme for parsing scope correctly
            url_to_parse = url
            if "://" not in url:
                 # Use the scheme from the *target* domain info if available
                 default_scheme = target_domain_info.get('scheme', 'http')
                 url_to_parse = f"{default_scheme}://" + url

            parsed_link = urlparse(url_to_parse)
            if parsed_link.scheme not in ("http", "https"):
                 return False # Skip non-web links

            # Handle cases where target domain is just a hostname (IP, localhost)
            if not target_domain_info.get("domain"): # Check if 'domain' part is empty
                 # Fallback to comparing exact netloc (hostname:port)
                 return parsed_link.netloc.lower() == target_domain_info["netloc"]

            # Standard comparison using registered domain
            extracted = tldextract.extract(url_to_parse)
            link_registered_domain = extracted.registered_domain.lower()

            # Allow if link's registered domain matches target's registered domain
            return link_registered_domain == target_domain_info["registered_domain"]

        except Exception as e:
            logger.warning(f"Error checking scope for URL {url}: {e}")
            return False


class FunnelPageClassifier:
    """Classifies pages based on URL and content using pre-compiled regex patterns."""
    def __init__(self, patterns: PagePatterns):
        self.patterns_config = patterns
        self._compiled_patterns: Dict[PageClassificationType, List[re.Pattern]] = {}
        self._compiled_hidden_patterns: List[re.Pattern] = []
        # Content analysis patterns (can reuse or define specific ones)
        self._compiled_payment_patterns: List[re.Pattern] = []
        self._compiled_price_patterns: List[re.Pattern] = []

        self._compile_patterns()
        self._classification_cache: Dict[str, FrozenSet[PageClassificationType]] = {}

    def _compile_patterns(self):
        """Compiles all regex patterns for efficiency."""
        pattern_map = {
            PageClassificationType.THANK_YOU: self.patterns_config.thank_you,
            PageClassificationType.UPSELL: self.patterns_config.upsell,
            PageClassificationType.DOWNSELL: self.patterns_config.downsell,
            PageClassificationType.CHECKOUT: self.patterns_config.checkout,
            PageClassificationType.LEAD_CAPTURE: self.patterns_config.lead_capture,
            PageClassificationType.WEBINAR: self.patterns_config.webinar,
            PageClassificationType.MEMBERS_AREA: self.patterns_config.members_area,
            # Add new Enum types if they have distinct URL patterns
            PageClassificationType.ORDER_CONFIRMATION: self.patterns_config.thank_you, # Reuse Thank You patterns initially
            PageClassificationType.RECEIPT: self.patterns_config.thank_you,            # Reuse Thank You patterns initially
            PageClassificationType.ORDER_FORM: self.patterns_config.checkout        # Reuse Checkout patterns initially
        }
        for page_type, patterns_list in pattern_map.items():
            try:
                compiled = [re.compile(p, re.IGNORECASE | re.UNICODE) for p in patterns_list]
                self._compiled_patterns[page_type] = compiled
            except re.error as e:
                logger.error(f"Invalid regex pattern for {page_type}: '{e.pattern}' - {e.msg}")
                self._compiled_patterns[page_type] = [] # Use empty list if compilation fails

        try:
            self._compiled_hidden_patterns = [re.compile(p, re.IGNORECASE | re.UNICODE) for p in self.patterns_config.hidden_indicators]
        except re.error as e:
            logger.error(f"Invalid regex pattern for hidden indicators: '{e.pattern}' - {e.msg}")
            self._compiled_hidden_patterns = []

        # Compile content patterns separately
        try:
             # Simple keyword check for payment indicators (case-insensitive)
             self._compiled_payment_patterns = [re.compile(r'\b' + re.escape(kw) + r'\b', re.IGNORECASE | re.UNICODE) for kw in self.patterns_config.payment_form_indicators]
        except re.error as e:
             logger.error(f"Invalid regex pattern for payment indicators: '{e.pattern}' - {e.msg}")
             self._compiled_payment_patterns = []

        try:
             self._compiled_price_patterns = [re.compile(p, re.IGNORECASE | re.UNICODE) for p in self.patterns_config.price_patterns]
        except re.error as e:
             logger.error(f"Invalid regex pattern for price patterns: '{e.pattern}' - {e.msg}")
             self._compiled_price_patterns = []

        logger.info("Regex patterns compiled for URL and content classification.")


    def classify_page(self, url: str, page_title: Optional[str] = None, page_content: Optional[str] = None) -> FrozenSet[PageClassificationType]:
        """Classifies a page based on URL, Title, and Content."""
        # Use URL as primary cache key, assuming content doesn't change classification drastically
        cache_key = url
        if cache_key in self._classification_cache:
            return self._classification_cache[cache_key]

        url_lower = url.lower()
        title_lower = page_title.lower() if page_title else ""
        classifications: Set[PageClassificationType] = set()

        # 1. Classify based on URL patterns
        for pt, patterns in self._compiled_patterns.items():
            # Skip meta-types or derived types during direct URL matching if handled separately
            if pt.name.startswith('CONTENT_'): continue
            if any(p.search(url_lower) for p in patterns):
                classifications.add(pt)
                # Optional: Refine based on specificity (e.g., prefer ORDER_CONFIRMATION over THANK_YOU if both match?)
                # For now, allow multiple classifications based on URL patterns

        # 2. Check for hidden indicators in URL
        if any(p.search(url_lower) for p in self._compiled_hidden_patterns):
            classifications.add(PageClassificationType.HIDDEN_BY_URL)

        # 3. Classify based on Content / Title (if content available)
        if page_content:
            content_lower = page_content.lower() # Lowercase once for efficiency
            text_to_search = title_lower + " " + content_lower # Combine for easier searching

            content_map = {
                PageClassificationType.CONTENT_THANK_YOU: self._compiled_patterns.get(PageClassificationType.THANK_YOU, []),
                PageClassificationType.CONTENT_UPSELL: self._compiled_patterns.get(PageClassificationType.UPSELL, []),
                PageClassificationType.CONTENT_DOWNSELL: self._compiled_patterns.get(PageClassificationType.DOWNSELL, []),
                PageClassificationType.CONTENT_CHECKOUT: self._compiled_patterns.get(PageClassificationType.CHECKOUT, []),
                PageClassificationType.CONTENT_LEAD_CAPTURE: self._compiled_patterns.get(PageClassificationType.LEAD_CAPTURE, []),
                PageClassificationType.CONTENT_WEBINAR: self._compiled_patterns.get(PageClassificationType.WEBINAR, []),
                PageClassificationType.CONTENT_MEMBERS_AREA: self._compiled_patterns.get(PageClassificationType.MEMBERS_AREA, [])
                # Add CONTENT versions for new types if needed, reusing patterns
            }

            for content_pt, patterns in content_map.items():
                # Check if corresponding URL type is *not* already found? Or always add content type? Always add.
                # url_pt = PageClassificationType[content_pt.name.replace('CONTENT_', '')] # Get corresponding URL type
                if any(p.search(text_to_search) for p in patterns):
                     classifications.add(content_pt)

        # Refinement: Remove less specific types if more specific ones are present
        # Example: If ORDER_CONFIRMATION is present, remove THANK_YOU?
        if PageClassificationType.ORDER_CONFIRMATION in classifications or PageClassificationType.RECEIPT in classifications:
            classifications.discard(PageClassificationType.THANK_YOU)
        if PageClassificationType.ORDER_FORM in classifications:
             classifications.discard(PageClassificationType.CHECKOUT)
        # Same for Content versions?
        if PageClassificationType.CONTENT_THANK_YOU in classifications and \
           any(c in classifications for c in [PageClassificationType.ORDER_CONFIRMATION, PageClassificationType.RECEIPT]):
             classifications.discard(PageClassificationType.CONTENT_THANK_YOU)


        # If no other classification is found, mark as Unknown
        if not classifications:
            classifications.add(PageClassificationType.UNKNOWN)

        result = frozenset(classifications)
        self._classification_cache[cache_key] = result
        return result

    def analyze_content_features(self, page_content: str) -> Tuple[bool, List[str]]:
        """Analyzes page content for payment and pricing indicators."""
        content_lower = page_content.lower()
        has_payment = any(p.search(content_lower) for p in self._compiled_payment_patterns)

        prices_found = []
        if self._compiled_price_patterns:
             # Limit number of prices found to avoid excessive lists for long pages
             max_prices = 20
             for p in self._compiled_price_patterns:
                 matches = p.findall(content_lower)
                 for match in matches:
                      # Clean up match if needed (e.g., strip whitespace)
                      cleaned_match = match.strip()
                      if cleaned_match and cleaned_match not in prices_found:
                           prices_found.append(cleaned_match)
                      if len(prices_found) >= max_prices: break
                 if len(prices_found) >= max_prices: break

        has_pricing = bool(prices_found)
        return has_payment, prices_found


class WebsiteCrawler:
    """Asynchronous website crawler with advanced discovery techniques."""
    def __init__(self, config: CrawlerConfig, classifier: FunnelPageClassifier):
        self.config = config
        self.classifier = classifier
        self.domain_info = config.get_domain_info() # Call method to get/calculate info
        self.patterns_config = config.page_patterns

        # State tracking
        self.crawl_queue: asyncio.Queue[Tuple[str, str]] = asyncio.Queue() # (URL, discovery_method)
        self.visited_keys: Set[str] = set()
        self.queued_keys: Set[str] = set() # Keep track of keys *added* to queue to reduce duplicates
        self.processing_urls: Set[str] = set() # Track keys currently being fetched/processed
        self.page_data: Dict[str, PageData] = {} # Stores PageData objects, keyed by canonical URL key
        self.page_relationships: Dict[str, Set[Tuple[str, str]]] = defaultdict(set) # source_key -> set of (target_url, link_text)
        self.page_variations: Dict[str, Set[str]] = defaultdict(set) # key -> set of original URLs pointing to it
        self.discovery_log: Dict[str, str] = {} # url_key -> first discovery_method

        # Other components (Robots, Semaphore, etc.)
        self._robots_parsers: Dict[str, Optional[RobotFileParser]] = {} # Cache parsers per netloc, Optional allows caching failures
        self._robots_fetch_lock = asyncio.Lock()
        self._sitemap_fetch_lock = asyncio.Lock() # Although sitemaps handled per-URL now, might be useful
        self._semaphore = asyncio.Semaphore(config.concurrent_requests)
        self._js_semaphore = asyncio.Semaphore(max(1, config.concurrent_requests // 2)) # Limit concurrent JS downloads

        # Progress/Stats
        self._processed_count = 0 # URLs attempted (dequeued)
        self._fetched_count = 0   # URLs successfully fetched (status code received)
        self._start_time = 0.0
        self._guessed_urls_added = 0
        self._js_urls_added = 0
        self._sitemap_urls_added = 0
        self._queue_size_for_progress = 0 # Keep track of queue size for display

        # Parsing helpers
        self._link_strainer = SoupStrainer('a', href=True)
        self._script_strainer = SoupStrainer('script', src=True) # For finding external JS files
        self._form_strainer = SoupStrainer('form')

        # Streamlit callback
        self.progress_callback: Optional[Callable[[int, int, int, int, str], None]] = None # processed, fetched, total, queue_size, status_text

    def set_progress_callback(self, callback: Callable[[int, int, int, int, str], None]):
        """Sets the callback function for Streamlit progress updates."""
        self.progress_callback = callback

    def _update_progress(self, status_text: str = "Crawling..."):
        """ Safely calls the progress callback for Streamlit """
        if self.progress_callback:
             try:
                 self._queue_size_for_progress = self.crawl_queue.qsize() # Get current queue size
                 estimated_total = max(self.config.max_pages, len(self.queued_keys) + len(self.visited_keys)) # Dynamic total estimate
                 # Pass counts and queue size
                 self.progress_callback(
                     self._processed_count,
                     self._fetched_count,
                     self.config.max_pages, # Use max_pages as the consistent total for the progress bar
                     self._queue_size_for_progress,
                     status_text
                 )
             except Exception as cb_e:
                 logger.warning(f"Progress callback failed: {cb_e}")

    async def _enqueue_url(self, url: str, discovery_method: str, source_url: Optional[str] = None):
        """Adds a URL to the queue if valid, in scope, and not already visited/queued."""
        try:
            url = url.strip()
            # Basic sanity checks
            if not url or url.startswith(('#', 'javascript:', 'mailto:', 'tel:', 'data:')):
                return

            # Attempt to resolve relative URLs using source_url if provided
            if source_url and not urlparse(url).scheme and not urlparse(url).netloc:
                 try:
                      absolute_url = urljoin(source_url, url)
                 except ValueError:
                      logger.debug(f"Could not resolve relative URL '{url}' against base '{source_url}'")
                      return # Skip if resolution fails
            else:
                 absolute_url = url # Assume already absolute or resolvable by itself

            # Ensure scheme for validation and scope check (use target domain scheme as default)
            url_to_check = absolute_url
            if "://" not in url_to_check:
                 default_scheme = self.domain_info.get('scheme', 'http')
                 url_to_check = f"{default_scheme}://" + url_to_check

            # Validate scheme
            parsed_url_check = urlparse(url_to_check)
            if parsed_url_check.scheme not in ('http', 'https'):
                 logger.debug(f"Skipping non-http(s) URL ({parsed_url_check.scheme}) from {discovery_method}: {url}")
                 return

            # Check scope BEFORE generating key (more efficient)
            if not UrlUtils.is_within_scope(url_to_check, self.domain_info):
                 logger.debug(f"Skipping out-of-scope URL from {discovery_method}: {url}")
                 return

            # Generate canonical key using the URL with scheme
            url_key = UrlUtils.get_crawl_key(url_to_check)

            # Check visited and queued sets using the canonical key
            if url_key in self.visited_keys or url_key in self.queued_keys:
                 # Record variation even if not queueing again
                 if url_key in self.page_data or url_key in self.queued_keys:
                      self.page_variations[url_key].add(url) # Add original non-canonical url as a variation
                 return

            # Add the absolute URL (potentially resolved) to the queue
            await self.crawl_queue.put((absolute_url, discovery_method))
            self.queued_keys.add(url_key)
            if url_key not in self.discovery_log: # Log first discovery method
                self.discovery_log[url_key] = discovery_method
            # Record the variation that led to this key being queued
            self.page_variations[url_key].add(url)

            logger.debug(f"Enqueued ({discovery_method}): {absolute_url} (Key: {url_key})")

            # Track counts for stats
            if discovery_method == "Sitemap": self._sitemap_urls_added += 1
            elif discovery_method == "Guess": self._guessed_urls_added += 1
            elif discovery_method == "JavaScript": self._js_urls_added += 1

            # Update progress slightly later, maybe in the worker just before fetch?
            # Or just update queue size? Let _update_progress handle it.

        except Exception as e:
            logger.warning(f"Error enqueuing URL '{url}' (Source: {source_url}, Method: {discovery_method}): {e}")

    # --- FIX 1: Implement _can_fetch ---
    def _can_fetch(self, url: str, robot_parser: Optional[RobotFileParser]) -> bool:
        """Checks if crawling the URL is allowed by robots.txt."""
        if not self.config.respect_robots_txt:
            return True
        if robot_parser is None: # Handle case where robots.txt failed to fetch/parse
            logger.debug(f"No valid robots.txt parser available for {url}, allowing fetch.")
            return True # Fail open if parser doesn't exist
        try:
            # RobotFileParser expects the full URL
            allowed = robot_parser.can_fetch(self.config.user_agent, url)
            logger.debug(f"Robots.txt check for {url} using UA '{self.config.user_agent}': {'Allowed' if allowed else 'Disallowed'}")
            return allowed
        except Exception as e:
            logger.warning(f"Error checking robots.txt allowance for {url}: {e}. Allowing fetch as fallback.")
            return True # Fail open (allow crawling) if robots check fails unexpectedly

    async def _get_robots_parser(self, session: aiohttp.ClientSession, netloc: str) -> Optional[RobotFileParser]:
        """Fetches and parses robots.txt for the given netloc, trying HTTPS and HTTP. Caches results (including failures)."""
        if netloc in self._robots_parsers:
            logger.debug(f"Using cached robots.txt parser for {netloc}")
            return self._robots_parsers[netloc]

        async with self._robots_fetch_lock:
            # Double check cache after acquiring lock
            if netloc in self._robots_parsers:
                 return self._robots_parsers[netloc]

            parser = RobotFileParser()
            # Set default to allow *initially* only if we fail to fetch/parse *any* robots.txt
            parser.allow_all = False # Assume disallowed until successfully parsed or determined non-existent

            fetched_successfully = False
            parsed_successfully = False

            # Prefer HTTPS, then try HTTP
            for scheme in ["https", "http"]:
                 robots_url = f"{scheme}://{netloc}/robots.txt"
                 logger.info(f"Attempting to fetch robots.txt from {robots_url}")
                 try:
                      # Use a shorter timeout for robots.txt
                      robot_timeout = aiohttp.ClientTimeout(total=max(5.0, self.config.timeout / 4))
                      async with session.get(robots_url, timeout=robot_timeout, headers={'User-Agent': self.config.user_agent}, allow_redirects=True, max_redirects=3) as response:
                           # Consider any 2xx status as success for fetching content
                           if 200 <= response.status < 300:
                                content = await response.text(encoding='utf-8', errors='ignore')
                                fetched_successfully = True # Mark as fetched
                                try:
                                    parser.parse(content.splitlines())
                                    parsed_successfully = True # Mark as parsed
                                    logger.info(f"Successfully parsed robots.txt for {netloc} from {response.url}")
                                    # Don't set allow_all here, let can_fetch work naturally
                                    break # Stop after first successful parse
                                except Exception as parse_err:
                                    logger.error(f"Failed to parse robots.txt content from {response.url}: {parse_err}")
                                    # Continue loop? Maybe the HTTP version is valid? Let's break, assume malformed is an issue.
                                    break

                           # 4xx indicates robots.txt doesn't exist or we're denied access
                           elif 400 <= response.status < 500:
                                logger.info(f"robots.txt not found or access denied at {robots_url} (Status: {response.status}). Allowing all for this host.")
                                fetched_successfully = True # We got a definitive answer (it's not there)
                                parser.allow_all = True # Explicitly allow if not found/forbidden
                                break # Stop checking other schemes
                           else:
                                logger.warning(f"robots.txt inaccessible at {robots_url} (Status: {response.status}). Trying other scheme if available.")
                                # Continue loop to try other scheme (e.g., if HTTPS failed)

                 except asyncio.TimeoutError:
                     logger.warning(f"Timeout fetching {robots_url}.")
                 except aiohttp.ClientError as e:
                     logger.warning(f"ClientError fetching {robots_url}: {e}.")
                 except Exception as e:
                     logger.error(f"Unexpected error fetching/parsing {robots_url}: {e}", exc_info=True)
                     # Break here? If unexpected error, maybe better to assume allow?
                     parser.allow_all = True
                     break

            # Final decision on allow_all based on fetch/parse status
            if not fetched_successfully and not parsed_successfully:
                 logger.warning(f"Could not fetch or parse any robots.txt for {netloc}. Assuming allow all.")
                 parser.allow_all = True
            elif fetched_successfully and not parsed_successfully and not parser.allow_all:
                 # This case means we fetched something but failed to parse it, and didn't hit a 4xx
                 logger.warning(f"Fetched robots.txt for {netloc} but failed to parse. Rules may not be applied correctly.")
                 # Keep allow_all=False, can_fetch might still work partially or fail safe (disallow)

            self._robots_parsers[netloc] = parser if (fetched_successfully or parsed_successfully) else None # Cache None if complete failure
            return self._robots_parsers[netloc]


    async def _fetch_and_parse_sitemap(self, session: aiohttp.ClientSession, sitemap_url: str):
        """Recursively fetches and parses sitemaps/sitemap indexes."""
        if not self.config.find_sitemaps: return
        if not UrlUtils.is_within_scope(sitemap_url, self.domain_info):
             logger.debug(f"Skipping out-of-scope sitemap: {sitemap_url}")
             return

        sitemap_key = UrlUtils.get_crawl_key(sitemap_url)
        if sitemap_key in self.visited_keys: # Use visited_keys to track processed sitemaps too
             logger.debug(f"Skipping already processed sitemap: {sitemap_url}")
             return
        self.visited_keys.add(sitemap_key) # Mark as visited/processed early

        logger.info(f"Fetching sitemap: {sitemap_url}")
        self._update_progress(f"Fetching sitemap: {sitemap_url}")

        try:
            # Ensure sitemap URL has scheme for request
            parsed_sitemap_url = urlparse(sitemap_url)
            if not parsed_sitemap_url.scheme:
                sitemap_url = "http://" + sitemap_url # Default scheme if missing

            # Use semaphore to limit concurrent sitemap requests as well
            async with self._semaphore:
                 # Use a slightly longer timeout for potentially large sitemaps
                 sitemap_timeout = aiohttp.ClientTimeout(total=self.config.timeout * 1.5)
                 async with session.get(sitemap_url, timeout=sitemap_timeout, headers={'User-Agent': self.config.user_agent}, allow_redirects=True, max_redirects=5) as response:
                     final_sitemap_url = str(response.url)
                     if response.status == 200:
                         content = await response.read() # Read bytes for XML parsing
                         content_type = response.headers.get('Content-Type', '').lower()

                         # Check content type OR file extension (after redirects)
                         is_xml_type = 'xml' in content_type
                         is_xml_extension = final_sitemap_url.lower().endswith(('.xml', '.xml.gz'))
                         # Add check for plain text containing XML tags as fallback
                         is_likely_xml = is_xml_type or is_xml_extension or b'<urlset' in content[:100] or b'<sitemapindex' in content[:100]

                         if not is_likely_xml:
                              # Handle GZipped sitemaps (common)
                              if final_sitemap_url.lower().endswith('.gz'):
                                   try:
                                        import gzip
                                        content = gzip.decompress(content)
                                        logger.info(f"Decompressed gzipped sitemap: {final_sitemap_url}")
                                        is_likely_xml = b'<urlset' in content[:100] or b'<sitemapindex' in content[:100]
                                   except ImportError:
                                        logger.warning(f"Cannot decompress {final_sitemap_url}: `gzip` module not found?")
                                        return
                                   except gzip.BadGzipFile:
                                        logger.warning(f"Failed to decompress supposed gzip sitemap: {final_sitemap_url}")
                                        return
                                   except Exception as gz_err:
                                        logger.error(f"Error during gzip decompression for {final_sitemap_url}: {gz_err}")
                                        return

                         if not is_likely_xml:
                              logger.warning(f"Sitemap URL {final_sitemap_url} did not return XML content (Type: {content_type}). Skipping parse.")
                              return

                         # Parse XML content
                         try:
                              # Remove potential BOM (Byte Order Mark) which can break XML parser
                              if content.startswith(b'\xef\xbb\xbf'):
                                   content = content[3:]
                              root = ET.fromstring(content)
                              # Namespace handling - dynamically find namespace if possible
                              namespace = ''
                              match = re.match(r'\{([^}]+)\}', root.tag)
                              if match:
                                   namespace = match.group(1)
                                   logger.debug(f"Detected XML namespace: {namespace}")
                              ns = {'sm': namespace} if namespace else {}

                              # Find URLs in <url>/<loc> tags
                              urls = root.findall('.//sm:url/sm:loc', ns) if ns else root.findall('.//url/loc')
                              # Find sitemap locations in <sitemap>/<loc> tags (for index files)
                              sitemaps = root.findall('.//sm:sitemap/sm:loc', ns) if ns else root.findall('.//sitemap/loc')

                              url_count = 0
                              for url_element in urls:
                                   if url_element.text:
                                        # Enqueue with the sitemap as the source_url for relative resolution if needed (though sitemap URLs should be absolute)
                                        await self._enqueue_url(url_element.text.strip(), "Sitemap", source_url=final_sitemap_url)
                                        url_count +=1

                              sitemap_tasks = []
                              if sitemaps:
                                   logger.info(f"Found sitemap index at {final_sitemap_url}, processing {len(sitemaps)} sub-sitemaps.")
                                   for sitemap_loc in sitemaps:
                                        if sitemap_loc.text:
                                             # Recursively call fetch_and_parse
                                             sitemap_tasks.append(
                                                  self._fetch_and_parse_sitemap(session, urljoin(final_sitemap_url, sitemap_loc.text.strip()))
                                             )

                              if sitemap_tasks:
                                   await asyncio.gather(*sitemap_tasks, return_exceptions=True) # Handle errors in sub-tasks

                              logger.info(f"Processed sitemap {final_sitemap_url}: Found {url_count} URLs, {len(sitemaps)} sub-sitemaps.")

                         except ET.ParseError as e:
                              # Try to show snippet of content causing error
                              content_snippet = content[:200].decode('utf-8', errors='ignore')
                              logger.error(f"Failed to parse XML sitemap {final_sitemap_url}: {e}\nContent start: {content_snippet}...")
                         except Exception as e:
                              logger.error(f"Error processing sitemap {final_sitemap_url}: {e}", exc_info=True)

                     else:
                          logger.warning(f"Failed to fetch sitemap {sitemap_url} (final URL: {final_sitemap_url}), status: {response.status}")
        except asyncio.TimeoutError:
            logger.warning(f"Timeout fetching sitemap {sitemap_url}.")
        except aiohttp.ClientError as e:
            logger.warning(f"ClientError fetching sitemap {sitemap_url}: {e}.")
        except Exception as e:
            logger.error(f"Unexpected error fetching sitemap {sitemap_url}: {e}", exc_info=True)


    def _generate_guessed_urls(self, base_url: str) -> Set[str]:
        """Generates potential URLs based on common patterns relative to the base URL."""
        if not self.config.attempt_url_guessing or self._guessed_urls_added >= self.config.max_pages * 0.5: # Limit total guesses
            return set()

        guessed_urls = set()
        try:
            parsed = urlparse(base_url)
            scheme = parsed.scheme if parsed.scheme else 'http'
            netloc = parsed.netloc
            path_parts = [part for part in parsed.path.split('/') if part]

            # Generate base paths to try: /, /segment1/, /segment1/segment2/
            base_paths_to_try = ["/"] # Always include root
            current_path = ""
            for part in path_parts:
                current_path += "/" + part
                base_paths_to_try.append(current_path + "/") # Add with trailing slash

            generated_count = 0
            max_to_generate = self.config.max_guessed_urls_per_page # Limit per base URL

            # Try keywords relative to existing path segments and root
            for base in base_paths_to_try:
                if generated_count >= max_to_generate: break
                for keyword in COMMON_FUNNEL_KEYWORDS:
                    if generated_count >= max_to_generate: break
                    # Construct path guess: base + keyword
                    # Ensure clean joining (avoid double slashes)
                    path_guess = f"{base.rstrip('/')}/{keyword}"
                    for ext in COMMON_EXTENSIONS:
                        full_url = urlunparse((scheme, netloc, path_guess + ext, '', '', ''))
                        guessed_urls.add(full_url)
                        generated_count += 1
                        if generated_count >= max_to_generate: break

            logger.debug(f"Generated {len(guessed_urls)} guess URLs based on {base_url}")
            return guessed_urls # Return all generated for this page (up to limit)

        except Exception as e:
            logger.warning(f"Error generating guessed URLs for {base_url}: {e}")
            return set()


    async def _analyze_javascript_for_links(self, session: aiohttp.ClientSession, source_url: str, soup: BeautifulSoup):
        """Downloads and scans linked JS files for potential URLs."""
        if not self.config.analyze_javascript: return

        js_urls_to_fetch = set()
        # Find external scripts
        for script_tag in soup.find_all(self._script_strainer):
             src = script_tag.get('src')
             if src:
                 js_url = urljoin(source_url, src)
                 # Check scope *before* adding to fetch list
                 if UrlUtils.is_within_scope(js_url, self.domain_info):
                      js_urls_to_fetch.add(js_url)

        # Find inline scripts (more complex, basic check for now)
        inline_scripts = soup.find_all('script', src=None)
        inline_tasks = []
        if inline_scripts:
             logger.debug(f"Found {len(inline_scripts)} inline script tags to analyze on {source_url}")
             for script_tag in inline_scripts:
                 if script_tag.string:
                      # Process inline script content directly without fetching
                      inline_tasks.append(self._scan_js_content(script_tag.string, source_url, is_inline=True))

        if not js_urls_to_fetch and not inline_tasks: return

        logger.debug(f"Found {len(js_urls_to_fetch)} potential external JS files and {len(inline_tasks)} inline scripts to analyze from {source_url}")
        external_tasks = [self._fetch_and_scan_js(session, js_url, source_url) for js_url in js_urls_to_fetch]

        all_tasks = external_tasks + inline_tasks
        if all_tasks:
            await asyncio.gather(*all_tasks, return_exceptions=True)


    async def _fetch_and_scan_js(self, session: aiohttp.ClientSession, js_url: str, source_url: str):
        """Fetches a single external JS file and scans it using regex."""
        logger.debug(f"Fetching JS for analysis: {js_url}")
        try:
            # Use JS semaphore to limit concurrent downloads
            async with self._js_semaphore:
                 js_timeout = aiohttp.ClientTimeout(total=self.config.timeout)
                 async with session.get(js_url, timeout=js_timeout, headers={'User-Agent': self.config.user_agent}, allow_redirects=True, max_redirects=3) as response:
                     if response.status == 200:
                         js_content = await response.text(encoding='utf-8', errors='ignore')
                         await self._scan_js_content(js_content, source_url, js_url)
                     else:
                          logger.warning(f"Failed to fetch JS {js_url} for analysis, status: {response.status}")
        except asyncio.TimeoutError:
            logger.warning(f"Timeout fetching JS {js_url} for analysis.")
        except aiohttp.ClientError as e:
            logger.warning(f"ClientError fetching JS {js_url}: {e}.")
        except Exception as e:
            logger.error(f"Unexpected error fetching/analyzing JS {js_url}: {e}", exc_info=True)

    async def _scan_js_content(self, js_content: str, source_html_url: str, js_source_name: str = "Inline Script", is_inline: bool = False):
        """Scans JS content (either fetched or inline) for potential URLs."""
        log_prefix = f"JS Analysis ({js_source_name})"
        try:
            # Regex to find quoted strings that look like relative or absolute paths
            found_paths = set(m.group(1) for m in JS_URL_REGEX.finditer(js_content))

            if found_paths:
                logger.debug(f"{log_prefix}: Found {len(found_paths)} potential paths/URLs.")
                count = 0
                for path in found_paths:
                    try:
                        # Resolve relative to the *source HTML page* URL
                        # urljoin handles absolute paths correctly as well
                        potential_url = urljoin(source_html_url, path)
                        # Enqueue the resolved URL
                        await self._enqueue_url(potential_url, "JavaScript", source_url=source_html_url)
                        count += 1
                    except ValueError:
                        logger.debug(f"{log_prefix}: Could not resolve path '{path}'")
                if count > 0:
                    logger.info(f"{log_prefix}: Enqueued {count} URLs found via analysis.")
            #else: # Reduce noise: only log if paths were found
            #    logger.debug(f"{log_prefix}: No potential paths found matching regex.")

        except Exception as e:
            logger.error(f"{log_prefix}: Error scanning content: {e}", exc_info=True)


    # --- FIX 2: Implement _analyze_content ---
    def _analyze_content(self, url: str, soup: Optional[BeautifulSoup], content: Optional[str]) -> Tuple[bool, int, bool, bool, Tuple[str, ...]]:
        """Analyzes BeautifulSoup soup and raw content for forms, payment indicators, and pricing."""
        has_forms = False
        form_count = 0
        has_payment_indicators = False
        has_pricing_indicators = False
        prices_found: List[str] = []

        if soup:
            # 1. Analyze Forms
            forms = soup.find_all(self._form_strainer)
            form_count = len(forms)
            has_forms = form_count > 0

            # 2. Basic check within forms for payment-related input names/ids/placeholders
            #    (This is heuristic and might miss many cases or have false positives)
            if has_forms and content: # Need content for detailed check
                content_lower = content.lower() # Lowercase once
                if any(kw in content_lower for kw in self.patterns_config.payment_form_indicators):
                     has_payment_indicators = True
                # More specific check (optional):
                # for form in forms:
                #    if any(inp.get('name', '').lower() in ['cardnumber', 'cc-number', 'exp-date', 'cvc']
                #           or inp.get('id', '').lower() in ['cardnumber', 'cc-number', 'exp-date', 'cvc']
                #           for inp in form.find_all('input')):
                #        has_payment_indicators = True
                #        break


        # 3. Analyze Raw Content (if available) for Payment/Pricing using Classifier's methods
        if content:
             # Use the classifier's pre-compiled regexes for efficiency
             payment_found_in_content, prices_found_list = self.classifier.analyze_content_features(content)
             if payment_found_in_content:
                  has_payment_indicators = True # Found indicators anywhere in content
             prices_found = prices_found_list
             if prices_found:
                  has_pricing_indicators = True

        # Ensure prices_found is a tuple for the PageData dataclass
        prices_tuple = tuple(prices_found)

        logger.debug(f"Content analysis for {url}: Forms={form_count}, PaymentIndic={has_payment_indicators}, PricingIndic={has_pricing_indicators}, Prices={len(prices_tuple)}")
        return has_forms, form_count, has_payment_indicators, has_pricing_indicators, prices_tuple


    async def _fetch_and_process(self, url_tuple: Tuple[str, str], session: aiohttp.ClientSession) -> Optional[PageData]:
        """Fetches, processes a single URL, analyzes content, and triggers further discovery."""
        url, discovery_method = url_tuple
        self._processed_count += 1 # Increment when attempt starts

        # Ensure URL has scheme for processing. Use start URL's scheme as default.
        url_with_scheme = url
        if "://" not in url_with_scheme:
            default_scheme = self.domain_info.get('scheme', 'http')
            url_with_scheme = f"{default_scheme}://" + url_with_scheme

        # Generate key AFTER ensuring scheme
        crawl_key = UrlUtils.get_crawl_key(url_with_scheme)

        # Double-check if visited/processing SINCE being added to queue
        if crawl_key in self.visited_keys or crawl_key in self.processing_urls:
            logger.debug(f"Skipping {url} (Key: {crawl_key}): Already visited or processing.")
            self.page_variations[crawl_key].add(url) # Still record as variation
            # Mark task as done if skipping here? Queue should handle this.
            return None

        logger.debug(f"Processing URL: {url_with_scheme} (Key: {crawl_key}, Discovery: {discovery_method})")

        # Add to processing set
        self.processing_urls.add(crawl_key)
        self._update_progress(f"Fetching: {url_with_scheme}") # Update status

        # Initialize PageData arguments
        page_data_args: Dict[str, Any] = {
            "url": url, # Original URL requested
            "final_url": url_with_scheme, # Default final URL
            "crawl_key": crawl_key,
            "status_code": 0,
            "error_message": "Processing started but not completed", # Default error
            "discovery_method": self.discovery_log.get(crawl_key, discovery_method), # Use logged method
            "classifications": frozenset([PageClassificationType.ERROR]), # Default
            # Initialize all other fields to default/None
            "content_type": None, "title": "Processing...", "content_length": None,
            "has_forms": False, "form_count": 0, "has_payment_indicators": False,
            "has_pricing_indicators": False, "prices_found": tuple(), "redirect_history": tuple(),
            "crawl_timestamp": time.time()
        }

        start_req_time = time.monotonic()
        retries = 0
        redirect_history: List[str] = []
        current_url = url_with_scheme # Start fetch loop with URL containing scheme
        response_obj = None # To hold the response object

        try:
            # --- Robots.txt Check ---
            # Ensure we use the netloc from the potentially redirected URL if redirects occur
            # Do initial check here, re-check if redirected across subdomains? Less common.
            parsed_for_robots = urlparse(current_url)
            robots_parser = await self._get_robots_parser(session, parsed_for_robots.netloc)
            if not self._can_fetch(current_url, robots_parser):
                logger.info(f"Skipping disallowed URL by robots.txt: {current_url}")
                page_data_args.update({
                    "status_code": -1, # Use a specific code for robots blocked
                    "error_message": "Blocked by robots.txt",
                    "classifications": frozenset([PageClassificationType.ERROR]),
                    "final_url": current_url # Final URL is the one blocked
                })
                # No further processing needed
                return PageData(**page_data_args) # Return data indicating block


            # --- Main Fetch/Redirect Loop ---
            while True: # Loop handles retries and redirects
                logger.debug(f"Attempting fetch for {current_url} (Retry: {retries}, Redirects: {len(redirect_history)})")
                try:
                    async with self._semaphore: # Acquire semaphore before request
                         # Apply general request delay *before* making the request
                         base_delay = self.config.request_delay
                         jitter_amount = base_delay * self.config.request_delay_jitter
                         delay_with_jitter = base_delay + (random.uniform(-jitter_amount, jitter_amount) if jitter_amount > 0 else 0)
                         await asyncio.sleep(max(0, delay_with_jitter))

                         async with session.get(
                             current_url,
                             timeout=aiohttp.ClientTimeout(total=self.config.timeout),
                             headers={'User-Agent': self.config.user_agent},
                             allow_redirects=False # Handle redirects manually
                         ) as response:
                            response_obj = response # Store response for later access
                            self._fetched_count += 1 # Increment successful fetch attempts

                            # --- Manual Redirect Handling ---
                            if response.status in (301, 302, 303, 307, 308) and 'Location' in response.headers:
                                if len(redirect_history) >= self.config.max_redirects:
                                    logger.warning(f"Max redirects ({self.config.max_redirects}) exceeded for starting URL {url}")
                                    page_data_args["error_message"] = f"Max redirects exceeded (> {self.config.max_redirects})"
                                    page_data_args["status_code"] = response.status
                                    page_data_args["final_url"] = current_url # Last URL before error
                                    page_data_args["redirect_history"] = tuple(redirect_history)
                                    page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                    break # Exit the fetch loop

                                next_url_raw = response.headers['Location']
                                next_url = urljoin(current_url, next_url_raw) # Resolve relative redirects
                                logger.debug(f"Redirecting: {current_url} -> {next_url} (Status: {response.status})")
                                redirect_history.append(current_url)
                                current_url = next_url # Update URL for next iteration/final data

                                # Check scope of the *new* URL
                                if not UrlUtils.is_within_scope(current_url, self.domain_info):
                                    logger.info(f"Redirected out of scope to: {current_url}")
                                    page_data_args["error_message"] = f"Redirected out of scope to {current_url}"
                                    page_data_args["status_code"] = response.status
                                    page_data_args["final_url"] = current_url # Record the out-of-scope URL
                                    page_data_args["redirect_history"] = tuple(redirect_history)
                                    page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                    break # Exit fetch loop

                                # Check robots.txt for the *new* URL if domain/subdomain changes? Might be overkill.
                                # Generally, if allowed on entry, follow redirects.

                                # Continue redirect loop (don't increment retries)
                                continue # Go to next iteration of inner try/fetch loop

                            # --- Process Non-Redirect Response ---
                            page_data_args["final_url"] = str(response.url) # Should match current_url if no redirects happened
                            page_data_args["status_code"] = response.status
                            page_data_args["content_type"] = response.headers.get('Content-Type', '').lower().split(';')[0].strip()
                            page_data_args["redirect_history"] = tuple(redirect_history)

                            # Clear error message on successful status code range
                            if 200 <= response.status < 400: # Include 3xx non-redirects if any
                                page_data_args["error_message"] = None

                            # --- Process Successful Response (2xx) ---
                            if 200 <= response.status < 300:
                                page_data_args["content_length"] = response.content_length # From headers (might be None)

                                # Only parse HTML content
                                if 'html' in page_data_args["content_type"]:
                                    try:
                                        # Read content efficiently
                                        content_bytes = await response.read()
                                        # Decode carefully
                                        try:
                                             # Try decoding with detected encoding or fallback
                                             detected_encoding = response.get_encoding()
                                             content = content_bytes.decode(detected_encoding, errors='replace')
                                        except LookupError: # If encoding is unknown/invalid
                                             logger.warning(f"Unknown encoding '{response.charset}', falling back to utf-8 for {response.url}")
                                             content = content_bytes.decode('utf-8', errors='replace')

                                        if page_data_args["content_length"] is None:
                                             page_data_args["content_length"] = len(content_bytes)

                                        # --- FIX 6: Check soup object ---
                                        soup: Optional[BeautifulSoup] = None
                                        try:
                                             # Use SoupStrainer for initial parse? Maybe not needed if analyzing full content anyway.
                                             soup = BeautifulSoup(content, DEFAULT_PARSER)
                                             page_data_args["title"] = self._extract_page_title(soup) or "No Title Found"
                                        except Exception as bs_error:
                                             logger.error(f"BeautifulSoup failed to parse {response.url}: {bs_error}")
                                             page_data_args["error_message"] = f"HTML Parsing Error (BS4): {bs_error}"
                                             page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                             # Continue without soup if parsing fails? Or break? Let's continue.

                                        # Analyze content (even if soup failed, try raw content)
                                        (has_forms, form_count, has_payment, has_pricing, prices) = self._analyze_content(str(response.url), soup, content)
                                        page_data_args.update({
                                             "has_forms": has_forms, "form_count": form_count,
                                             "has_payment_indicators": has_payment,
                                             "has_pricing_indicators": has_pricing, "prices_found": prices
                                        })

                                        # Classify page based on URL, Title, and Content
                                        page_data_args["classifications"] = self.classifier.classify_page(str(response.url), page_data_args["title"], content)

                                        # --- Trigger Further Discovery on Success ---
                                        if soup: # Only extract links/js if soup is valid
                                            await self._extract_and_queue_html_links(str(response.url), soup)
                                            await self._analyze_javascript_for_links(session, str(response.url), soup)
                                        else:
                                             logger.warning(f"Skipping link/JS extraction for {response.url} due to parsing failure.")

                                        # Generate and queue guessed URLs based on this page
                                        guessed_urls = self._generate_guessed_urls(str(response.url))
                                        for guess_url in guessed_urls:
                                            await self._enqueue_url(guess_url, "Guess", source_url=str(response.url))

                                    except UnicodeDecodeError as decode_error:
                                        logger.error(f"Encoding error for {response.url}: {decode_error}")
                                        page_data_args["error_message"] = f"Encoding Error: {decode_error}"
                                        page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                    except Exception as parse_error:
                                         logger.error(f"Error processing HTML content for {response.url}: {parse_error}", exc_info=True)
                                         page_data_args["error_message"] = f"Content Processing Error: {parse_error}"
                                         page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                else:
                                    # Non-HTML content
                                    logger.debug(f"Skipping content analysis for non-HTML type: {page_data_args['content_type']} at {response.url}")
                                    page_data_args["classifications"] = frozenset([PageClassificationType.UNKNOWN])
                                    # Ensure error is None if status was 2xx
                                    page_data_args["error_message"] = None

                                break # Success (2xx)! Exit the retry/redirect loop.

                            # --- Handle Client Errors (4xx) ---
                            elif 400 <= response.status < 500:
                                error_reason = response.reason or f"HTTP Client Error"
                                page_data_args["error_message"] = f"HTTP {response.status} {error_reason}"
                                page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                logger.warning(f"{error_reason} ({response.status}) for {current_url}. No retries.")
                                break # No retry for 4xx errors, exit loop.

                            # --- Handle Server Errors (5xx) ---
                            elif 500 <= response.status < 600:
                                error_reason = response.reason or f"HTTP Server Error"
                                page_data_args["error_message"] = f"HTTP {response.status} {error_reason}"
                                page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                logger.warning(f"{error_reason} ({response.status}) for {current_url}. Will retry if attempts remain.")
                                # Loop will continue to retry logic below

                            else: # Other unexpected status codes
                                error_reason = response.reason or f"Unexpected HTTP Status"
                                page_data_args["error_message"] = f"HTTP {response.status} {error_reason}"
                                page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                                logger.warning(f"Unexpected status {response.status} ({error_reason}) for {current_url}. Check retry logic.")
                                # Loop will continue to retry logic below

                # --- Exception Handling for Fetch Attempt ---
                except (aiohttp.ClientConnectionError, aiohttp.ClientPayloadError, asyncio.TimeoutError) as network_error:
                    err_type = type(network_error).__name__
                    logger.warning(f"{err_type} for {current_url} (Attempt {retries+1}/{self.config.max_retries+1}): {network_error}")
                    page_data_args["error_message"] = f"Network Error: {err_type}"
                    page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                    page_data_args["status_code"] = 0 # Indicate network level failure
                except aiohttp.ClientError as client_err: # Catch other client errors (e.g., invalid URL structure at HTTP level)
                    err_type = type(client_err).__name__
                    logger.warning(f"{err_type} for {current_url} (Attempt {retries+1}/{self.config.max_retries+1}): {client_err}")
                    page_data_args["error_message"] = f"Client Error: {err_type}"
                    page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                    page_data_args["status_code"] = 0
                    # Break here? Usually ClientError is not retryable unless transient. Let's break.
                    break
                except Exception as e: # Catch-all for unexpected errors during fetch/response handling
                    err_type = type(e).__name__
                    logger.exception(f"Unexpected error processing {current_url} (Attempt {retries+1}): {e}")
                    page_data_args["error_message"] = f"Unexpected Error: {err_type}: {str(e)[:100]}"
                    page_data_args["classifications"] = frozenset([PageClassificationType.ERROR])
                    page_data_args["status_code"] = 0
                    break # Don't retry on unexpected errors

                # --- Retry Logic ---
                retries += 1
                if retries > self.config.max_retries:
                    logger.error(f"Max retries ({self.config.max_retries}) exceeded for URL {url} (last attempt: {current_url}). Final error: {page_data_args['error_message']}")
                    break # Exit retry loop

                # Check if the error code suggests retrying (e.g., 5xx, network errors)
                # 4xx and success codes already broke the loop
                if page_data_args["status_code"] != 0 and not (500 <= page_data_args["status_code"] < 600):
                     logger.debug(f"Not retrying for status {page_data_args['status_code']} on {current_url}")
                     break # Don't retry if not a server error or network error

                # Calculate retry delay with jitter
                base_retry_delay = 0.5 * (2 ** (retries - 1)) # Exponential backoff
                jitter = base_retry_delay * 0.3
                actual_delay = base_retry_delay + random.uniform(-jitter, jitter)
                clamped_delay = max(0.2, min(actual_delay, 15.0)) # Clamp delay between 0.2s and 15s
                logger.info(f"Retrying ({retries}/{self.config.max_retries}) URL: {current_url} after {clamped_delay:.2f}s delay due to: {page_data_args['error_message']}")
                await asyncio.sleep(clamped_delay)
                # Reset error message for next retry attempt? Or keep last error? Keep last error.

        finally:
            # --- Finalize Page Processing ---
            req_duration = time.monotonic() - start_req_time

            # Construct the final PageData object
            final_page_data = PageData(**page_data_args)

            # Get the key for the *final* URL after redirects
            final_url_key = UrlUtils.get_crawl_key(final_page_data.final_url)

            # Store data using the *final* URL's key
            self.page_data[final_url_key] = final_page_data

            # Update variations: Original key might differ from final key
            self.page_variations[crawl_key].add(url) # Add original URL to variations for the initial key
            if final_url_key != crawl_key:
                self.page_variations[final_url_key].add(final_page_data.final_url) # Add final URL if key changed
                # Also add the original URL to the final key's variations if it's different
                self.page_variations[final_url_key].add(url)

            # Add both initial and final keys to visited set
            self.visited_keys.add(crawl_key)
            if final_url_key != crawl_key:
                self.visited_keys.add(final_url_key)

            # Log discovery method for both keys if they differ
            if crawl_key not in self.discovery_log:
                self.discovery_log[crawl_key] = discovery_method
            if final_url_key != crawl_key and final_url_key not in self.discovery_log:
                # Mark discovery as related to the original method via redirect
                self.discovery_log[final_url_key] = f"Redirect/{self.discovery_log.get(crawl_key, discovery_method)}"

            # Remove initial key from processing set
            self.processing_urls.discard(crawl_key) # Use discard to avoid error if already removed

            # Log processing outcome
            status_symbol = "✅" if 200 <= final_page_data.status_code < 300 else "❌" if final_page_data.status_code >= 400 or final_page_data.error_message else "⚠️" # Use warning for redirects, etc.
            log_message = (
                f"Processed ({self._processed_count}/{self.config.max_pages}) {status_symbol} "
                f"[{final_page_data.status_code if final_page_data.status_code > 0 else 'ERR'}] "
                f"{final_page_data.final_url} ({req_duration:.2f}s) "
                f"-> {', '.join(map(str, final_page_data.classifications))}"
            )
            if final_page_data.error_message:
                 log_message += f" (Error: {final_page_data.error_message})"
            if final_page_data.redirect_history:
                 log_message += f" (Redirected from: {final_page_data.redirect_history[0] if final_page_data.redirect_history else 'N/A'})"

            logger.info(log_message)

            # Delay moved to *before* the request within the semaphore context

        return final_page_data


    def _extract_page_title(self, soup: BeautifulSoup) -> Optional[str]:
         """Extracts the page title from the soup."""
         try:
             title_tag = soup.find('title')
             if title_tag and title_tag.string:
                 return title_tag.string.strip()
             # Fallback: Try H1 tag?
             h1_tag = soup.find('h1')
             if h1_tag and h1_tag.string:
                 return h1_tag.string.strip()
         except Exception as e:
             logger.warning(f"Error extracting title: {e}")
         return None


    async def _extract_and_queue_html_links(self, source_url: str, soup: BeautifulSoup):
        """Extracts standard HTML links (<a> tags) and queues them."""
        links_added = 0
        source_key = UrlUtils.get_crawl_key(source_url) # Key of the page containing the links

        for link_tag in soup.find_all(self._link_strainer): # Use pre-defined strainer
            try:
                href = link_tag.get('href')
                if href:
                    # Resolve URL relative to the source page
                    # Enqueue handles scheme adding, scope check, duplicate check etc.
                    await self._enqueue_url(href, "Link", source_url=source_url)

                    # Store relationship (source_key -> target_url_original, link_text)
                    link_text = link_tag.get_text(strip=True)
                    link_text_short = (link_text[:75] + '...') if len(link_text) > 75 else link_text

                    # Resolve target URL again for relationship storage consistency? Or store original href? Store original href.
                    target_url_for_relation = href # Store the original href attribute value

                    # Ensure source_key exists in page_data before adding relationship?
                    # It should exist as this function is called after processing the source page.
                    if source_key in self.page_data or source_key in self.processing_urls or source_key in self.queued_keys:
                        self.page_relationships[source_key].add((target_url_for_relation, link_text_short))
                        links_added += 1
                    else:
                         logger.warning(f"Source key {source_key} (from {source_url}) not found while recording relationship to {target_url_for_relation}")

            except Exception as e:
                logger.warning(f"Error processing link '{href[:100] if href else 'N/A'}' on {source_url}: {e}", exc_info=False) # Reduce log noise

        if links_added > 0:
            logger.debug(f"Processed {links_added} HTML links from {source_url}")


    async def _discover_initial_urls(self, session: aiohttp.ClientSession):
         """Finds sitemaps, adds manual URLs, and enqueues the start URL before starting workers."""
         initial_tasks = []
         start_url_str = str(self.config.start_url) # Should have scheme from validation

         # 1. Enqueue start URL
         logger.info(f"Enqueuing start URL: {start_url_str}")
         await self._enqueue_url(start_url_str, "Start")

         # 2. Enqueue manual URLs
         if self.config.manual_urls:
              logger.info(f"Enqueuing {len(self.config.manual_urls)} manual URLs...")
              for manual_url_obj in self.config.manual_urls:
                   await self._enqueue_url(str(manual_url_obj), "Manual")

         # 3. Find and parse sitemaps (if enabled)
         if self.config.find_sitemaps:
              logger.info("Attempting sitemap discovery...")
              parsed_start = urlparse(start_url_str)
              netloc = parsed_start.netloc
              if not netloc:
                   logger.error(f"Cannot determine netloc from start URL '{start_url_str}' for sitemap discovery. Skipping sitemaps.")
                   return # Cannot proceed without netloc

              # Fetch robots.txt first to check for sitemap directives
              robots_parser = await self._get_robots_parser(session, netloc)
              sitemap_urls_found = set()

              # Use hasattr for safety, check if sitemaps attribute exists and is not None/empty
              if robots_parser and hasattr(robots_parser, 'sitemaps') and robots_parser.sitemaps:
                   logger.info(f"Found sitemap directives in robots.txt: {robots_parser.sitemaps}")
                   for s_url in robots_parser.sitemaps:
                       # Resolve relative sitemap URLs from robots.txt against the start URL's domain
                       sitemap_urls_found.add(urljoin(start_url_str, s_url))

              # Add default location(s) - try sitemap.xml at the root
              default_sitemap_path = '/sitemap.xml'
              default_sitemap_url = urlunparse((parsed_start.scheme, netloc, default_sitemap_path, '', '', ''))
              sitemap_urls_found.add(default_sitemap_url)
              # Optional: try common variations like /sitemap_index.xml?
              # default_sitemap_index_url = urlunparse((parsed_start.scheme, netloc, '/sitemap_index.xml', '', '', ''))
              # sitemap_urls_found.add(default_sitemap_index_url)

              logger.info(f"Potential sitemap locations to check: {sitemap_urls_found}")
              self._update_progress("Discovering Sitemaps...")
              for s_url in sitemap_urls_found:
                   # Add sitemap parsing tasks
                   initial_tasks.append(self._fetch_and_parse_sitemap(session, s_url))

         # Run initial discovery tasks (primarily sitemap fetching) concurrently
         if initial_tasks:
              logger.info(f"Running {len(initial_tasks)} sitemap discovery tasks...")
              try:
                    results = await asyncio.gather(*initial_tasks, return_exceptions=True)
                    # Log any exceptions from sitemap processing
                    for i, result in enumerate(results):
                         if isinstance(result, Exception):
                              logger.error(f"Error during initial sitemap task {i}: {result}")
              except Exception as gather_err:
                   logger.error(f"Error during initial sitemap discovery gather: {gather_err}")
              logger.info("Initial sitemap discovery tasks complete.")
         else:
              logger.info("No sitemap discovery tasks to run.")


    async def crawl(self) -> None:
        """Starts the website crawling process with enhanced discovery."""
        self._start_time = time.time()
        logger.info(f"Starting ELITE crawl for {self.config.start_url} (Max pages: {self.config.max_pages})")
        logger.info(f"Domain Info: {self.domain_info}")
        logger.info(f"Discovery Options: Sitemaps={self.config.find_sitemaps}, Guessing={self.config.attempt_url_guessing}, JS_Analyze={self.config.analyze_javascript}")
        self._update_progress("Initializing...")

        # Setup connection pool with appropriate limits and SSL handling
        try:
            # --- FIX 3: Note about SSL ---
            # Using ssl=False disables certificate verification - convenient but less secure.
            # Consider adding an option or using a custom SSL context for production use.
            # ssl_context = ssl.create_default_context()
            # ssl_context.check_hostname = False
            # ssl_context.verify_mode = ssl.CERT_NONE
            # connector = aiohttp.TCPConnector(limit_per_host=self.config.concurrent_requests, ssl=ssl_context)
            connector = aiohttp.TCPConnector(
                 limit_per_host=self.config.concurrent_requests, # Limit concurrency per host
                 limit=self.config.concurrent_requests * 5, # Overall connection limit
                 ssl=False, # WARNING: Disables SSL verification
                 enable_cleanup_closed=True # Helps prevent resource leaks
            )
        except Exception as conn_err:
            logger.exception(f"Failed to create TCPConnector: {conn_err}")
            self._update_progress(f"Error: Failed network init")
            st.error(f"Network initialization failed: {conn_err}")
            return

        async with aiohttp.ClientSession(connector=connector, headers={'User-Agent': self.config.user_agent}) as session:

            await self._discover_initial_urls(session) # Enqueue start/manual URLs, find sitemaps

            logger.info(f"Initial queue size after discovery: {self.crawl_queue.qsize()}")
            if self.crawl_queue.empty():
                 logger.warning("No initial URLs found or enqueued (Start URL might be invalid, out of scope, or blocked?). Stopping crawl.")
                 self._update_progress("Failed: No starting URLs")
                 st.warning("Could not find any URLs to crawl, please check the Starting URL and configuration.", icon="⚠️")
                 return

            self._update_progress("Starting worker tasks...")
            workers = [asyncio.create_task(self._worker(f"Worker-{i+1}", session), name=f"Worker-{i+1}")
                       for i in range(self.config.concurrent_requests)]

            processed_last_check = -1
            queue_size_last_check = -1
            no_progress_counter = 0
            MAX_NO_PROGRESS_CHECKS = 8 # Increase stall detection threshold (e.g., ~16 seconds with 2s sleep)

            # --- Main Monitoring Loop ---
            while True:
                # Update progress regularly from monitor loop as well
                current_status = st.session_state.get('progress_status', 'Crawling...') # Get last known status
                self._update_progress(current_status) # Update with latest counts/queue size
                await asyncio.sleep(2) # Check status periodically

                q_size = self.crawl_queue.qsize()
                active_workers = sum(1 for w in workers if not w.done())
                active_processing = len(self.processing_urls)

                # Check stopping conditions
                if self._processed_count >= self.config.max_pages:
                    logger.info(f"Max pages ({self.config.max_pages}) processed limit reached. Stopping.")
                    break # Proceed to shutdown

                if q_size == 0 and active_processing == 0:
                    logger.info("Queue empty and no tasks processing. Checking worker status...")
                    # Wait a moment longer to ensure workers truly finish
                    await asyncio.sleep(0.5)
                    active_workers = sum(1 for w in workers if not w.done())
                    if active_workers == 0:
                        logger.info("Queue empty and all workers idle. Finishing.")
                        break # Crawl naturally completed
                    else:
                         logger.info(f"Queue empty, but {active_workers} workers still active (possibly finishing final tasks). Waiting...")


                # Stall detection - Check if processed count AND queue size haven't changed
                if self._processed_count == processed_last_check and q_size == queue_size_last_check and q_size == 0 and active_processing > 0:
                    no_progress_counter += 1
                    logger.warning(
                        f"Crawl might be stalled ({no_progress_counter}/{MAX_NO_PROGRESS_CHECKS}): "
                        f"Queue empty, {active_processing} URLs in processing state, "
                        f"{active_workers} workers active, processed count {self._processed_count} unchanged."
                    )
                    if no_progress_counter >= MAX_NO_PROGRESS_CHECKS:
                         logger.error(f"Crawl appears stalled for >{MAX_NO_PROGRESS_CHECKS*2} seconds. Stopping workers forcefully.")
                         # Log which URLs are stuck in processing
                         if self.processing_urls:
                              logger.error(f"URLs stuck in processing: {list(self.processing_urls)}")
                         break # Exit main loop due to stall
                elif self._processed_count != processed_last_check or q_size != queue_size_last_check:
                    no_progress_counter = 0 # Reset counter if progress is made (either processed or queue changed)

                processed_last_check = self._processed_count
                queue_size_last_check = q_size

            # --- Shutdown Phase ---
            logger.info("Shutting down crawl workers...")
            self._update_progress("Finishing up...")
            # Cancel any running worker tasks
            for task in workers:
                 if not task.done():
                      task.cancel()

            logger.info("Waiting for worker tasks to complete or cancel...")
            worker_results = await asyncio.gather(*workers, return_exceptions=True)
            for i, result in enumerate(worker_results):
                if isinstance(result, asyncio.CancelledError):
                    logger.debug(f"Worker-{i+1} successfully cancelled.")
                elif isinstance(result, Exception):
                    logger.error(f"Worker-{i+1} finished with an unhandled error: {result}", exc_info=result)
            logger.info("All worker tasks have completed or been cancelled.")

        # --- Post-Crawl Analysis ---
        self._identify_potential_hidden_pages()

        end_time = time.time()
        logger.info("-" * 40)
        logger.info(f"Crawl finished in {end_time - self._start_time:.2f} seconds.")
        logger.info(f"Attempted to process {self._processed_count} URLs.")
        logger.info(f"Successfully fetched {self._fetched_count} URLs (includes redirects/retries).")
        logger.info(f"Collected data for {len(self.page_data)} unique final pages (keys).")
        logger.info(f"Discovery Stats: Sitemap={self._sitemap_urls_added}, Guess={self._guessed_urls_added}, JS={self._js_urls_added}")
        logger.info(f"Found {len(self.page_relationships)} pages with outgoing HTML links.")
        error_count = sum(1 for d in self.page_data.values() if d.error_message or d.status_code >= 400)
        logger.info(f"Encountered errors on {error_count} pages.")
        logger.info("-" * 40)

        # ***** THIS IS THE CORRECTED LINE *****
        self._update_progress("Analysis Complete")
        # *************************************


    async def _worker(self, name: str, session: aiohttp.ClientSession):
        """Worker task that continuously fetches URLs from the queue."""
        logger.info(f"{name} started.")
        while True:
            # Check global stop condition (max pages) before getting item
            if self._processed_count >= self.config.max_pages:
                 logger.info(f"{name} stopping early: Max pages limit ({self.config.max_pages}) reached.")
                 break

            url_tuple = None # Ensure url_tuple is defined in scope
            try:
                # Wait for an item from the queue
                url_tuple = await self.crawl_queue.get()
                logger.debug(f"{name} got task: {url_tuple}")

                # Update progress *before* processing, reflecting the item taken from queue
                # This might cause the queue size in progress to seem off by 1 briefly, but reflects work starting
                self._update_progress(f"Fetching: {url_tuple[0]}")

                # Double check max pages *after* getting item, before processing
                if self._processed_count >= self.config.max_pages:
                     logger.info(f"{name} stopping: Max pages limit reached before processing {url_tuple[0]}. Task requeued implicitly by not calling task_done.")
                     # Don't call task_done, let monitor loop handle shutdown
                     break

                # Process the URL
                await self._fetch_and_process(url_tuple, session)

                # Mark task as done *after* successful processing or handling
                self.crawl_queue.task_done()

            except asyncio.CancelledError:
                 logger.info(f"{name} was cancelled.")
                 # If cancelled while holding an item, ensure task_done is called?
                 # No, the monitor loop handles cancellation globally.
                 break # Exit loop gracefully on cancellation
            except Exception as e:
                 logger.exception(f"{name} encountered unhandled error in worker loop for task {url_tuple}: {e}")
                 # Ensure task_done is called even if processing failed unexpectedly,
                 # otherwise the queue might never finish.
                 if url_tuple is not None: # Only call if we actually got a task
                     try:
                         self.crawl_queue.task_done()
                         logger.error(f"{name} marked task {url_tuple} as done despite unhandled exception.")
                     except ValueError: # Ignore if called too many times
                         pass
                     except asyncio.InvalidStateError: # Ignore if queue closed
                          pass
                 # Continue running? Or break? Let's continue for robustness.
                 await asyncio.sleep(1) # Short pause after error

        logger.info(f"{name} finished.")


    def _identify_potential_hidden_pages(self) -> None:
        """Identify potential hidden pages based on low incoming link count within the crawl."""
        if not self.page_data: return # Skip if no pages found

        logger.info("Analyzing incoming link frequency for potential hidden pages...")
        incoming_link_count = defaultdict(int)
        all_target_keys_linked_internally = set()

        # Build a map of all known URL keys from page_data
        all_page_keys = set(self.page_data.keys())

        for source_key, targets in self.page_relationships.items():
            # Only consider links originating from pages we actually crawled successfully
            if source_key not in all_page_keys:
                continue

            for target_url, _ in targets:
                # Resolve the target URL and get its key
                target_url_resolved = target_url
                # Need a base URL for resolution if target is relative - use source page's final URL
                source_page = self.page_data.get(source_key)
                if source_page and not urlparse(target_url_resolved).scheme:
                    try:
                         target_url_resolved = urljoin(source_page.final_url, target_url_resolved)
                    except ValueError: continue # Skip if invalid relative URL

                # Ensure target has scheme before getting key
                if "://" not in target_url_resolved:
                     # Use source page's scheme if possible, else default
                     scheme_to_use = urlparse(source_page.final_url).scheme if source_page else self.domain_info.get('scheme', 'http')
                     target_url_resolved = f"{scheme_to_use}://{target_url_resolved}"

                # Check scope again? Should be implicitly handled by only adding in-scope links.
                target_key = UrlUtils.get_crawl_key(target_url_resolved)

                # Increment count only if the target key corresponds to a crawled page
                if target_key in all_page_keys:
                    incoming_link_count[target_key] += 1
                    all_target_keys_linked_internally.add(target_key)

        hidden_found = 0
        updated_page_data = {}
        start_url_key = UrlUtils.get_crawl_key(str(self.config.start_url))

        for page_key, data in self.page_data.items():
            # Check if page is not the start page and has 0 or 1 incoming links found *during this crawl*
            # AND wasn't discovered via sitemap/guessing (might be intentionally unlinked)
            link_count = incoming_link_count.get(page_key, 0)
            is_start_page = (page_key == start_url_key)
            discovery_method = self.discovery_log.get(page_key, "")

            # Condition: Low link count, not start page, not explicitly found via sitemap/guess
            # Adjust threshold? Maybe link_count == 0 is better? Let's use <= 1 for now.
            if link_count <= 1 and not is_start_page:
                # Also check if it wasn't already classified as explicitly hidden by URL
                if PageClassificationType.HIDDEN_BY_URL not in data.classifications:
                    # Add POTENTIAL_HIDDEN classification
                    new_classifications = data.classifications | {PageClassificationType.POTENTIAL_HIDDEN}
                    # Use dataclasses.replace for immutability
                    updated_page_data[page_key] = dataclasses_replace(data, classifications=new_classifications)
                    hidden_found += 1
                    logger.debug(f"Marked {data.final_url} as POTENTIAL_HIDDEN (links: {link_count}, discovery: {discovery_method})")

        # Update the main page_data dictionary
        if updated_page_data:
             self.page_data.update(updated_page_data)
             logger.info(f"Identified {hidden_found} potentially hidden pages based on low internal link count.")
        else:
             logger.info("No additional potentially hidden pages identified based on link count.")


    def get_results(self) -> Tuple[Dict[str, PageData], Dict[str, Set[Tuple[str, str]]], Dict[str, Set[str]]]:
        """Return the collected crawl data."""
        # Return copies to prevent external modification? For performance, return direct refs.
        return self.page_data, self.page_relationships, self.page_variations


class FunnelAnalyzer:
    """Analyzes funnel structures based on crawled data using graph traversal."""
    def __init__(self, page_data: Dict[str, PageData], page_relationships: Dict[str, Set[Tuple[str, str]]], config: CrawlerConfig, discovery_log: Dict[str, str]):
        self.page_data = page_data
        self.page_relationships = page_relationships
        self.config = config
        self.discovery_log = discovery_log # Added discovery log
        self.start_url_key = UrlUtils.get_crawl_key(str(config.start_url))
        self._build_graph()
        logger.info(f"FunnelAnalyzer initialized: {len(page_data)} pages, {len(page_relationships)} sources with links.")

    def _build_graph(self):
        """Builds a directed graph (source_key -> set_of_target_keys) from relationships."""
        self.graph: Dict[str, Set[str]] = defaultdict(set)
        self.url_to_key_map: Dict[str, str] = {} # Map final URLs back to keys

        all_page_keys = set(self.page_data.keys())
        base_url_for_resolve = str(self.config.start_url) # Use start URL as base for resolving

        for source_key, targets in self.page_relationships.items():
            if source_key not in all_page_keys: continue # Source must be a crawled page

            source_page = self.page_data.get(source_key)
            source_final_url = source_page.final_url if source_page else base_url_for_resolve # Fallback base

            for target_url_original, _ in targets:
                # Resolve target URL relative to source page's final URL
                target_url_resolved = target_url_original
                try:
                    if not urlparse(target_url_resolved).scheme:
                         target_url_resolved = urljoin(source_final_url, target_url_resolved)
                except ValueError: continue # Skip invalid relative URLs

                # Ensure scheme before getting key
                if "://" not in target_url_resolved:
                     # Use source page's scheme if possible, else default
                     scheme_to_use = urlparse(source_final_url).scheme if source_final_url else self.config.get_domain_info().get('scheme', 'http')
                     target_url_resolved = f"{scheme_to_use}://{target_url_resolved}"


                target_key = UrlUtils.get_crawl_key(target_url_resolved)

                # Add edge only if the target key corresponds to a crawled page
                if target_key in all_page_keys:
                    self.graph[source_key].add(target_key)

        # Add nodes for pages that have no outgoing links recorded
        for key in all_page_keys:
            if key not in self.graph:
                self.graph[key] = set()
            # Populate URL to Key map
            page = self.page_data.get(key)
            if page:
                 self.url_to_key_map[page.final_url] = key

        link_count = sum(len(v) for v in self.graph.values())
        logger.info(f"Built analysis graph: {len(self.graph)} nodes (crawled pages), {link_count} internal directed edges.")


    def find_potential_funnel_flows(self, max_depth: int = 8, min_path_len: int = 2) -> List[List[Tuple[str, FrozenSet[PageClassificationType]]]]:
        """Finds potential funnel flows using Depth First Search from entry points."""
        potential_flows = []
        entry_points = self._identify_entry_points()

        if not entry_points:
            logger.warning("No potential funnel entry points identified. Cannot find flows.")
            return []
        if not self.graph:
             logger.warning("Analysis graph is empty. Cannot find flows.")
             return []

        logger.info(f"Starting funnel flow analysis from {len(entry_points)} entry points (max_depth={max_depth}, min_len={min_path_len}).")
        # Set to store hashes of paths found to avoid duplicates from different start points reaching the same path
        visited_paths_hashes: Set[int] = set()

        for start_key in entry_points:
            if start_key not in self.graph:
                logger.warning(f"Entry point key '{start_key}' not found in graph nodes, skipping.")
                continue

            # Use deque for DFS stack: (current_key, current_path_list)
            stack: deque[Tuple[str, List[str]]] = deque([(start_key, [start_key])])

            while stack:
                current_key, path = stack.pop() # DFS: pop from right

                # Check depth limit
                if len(path) > max_depth:
                    continue

                current_page = self.page_data.get(current_key)
                if not current_page:
                    logger.warning(f"Graph key '{current_key}' in path but not found in page_data. Path: {path}")
                    continue # Skip this path if data is missing

                current_classifications = current_page.classifications

                # --- Check for Path End Conditions ---
                # 1. Reached a terminal node type (Thank You, Members Area, Receipt etc.)
                is_terminal_node = any(c in current_classifications for c in [
                    PageClassificationType.THANK_YOU, PageClassificationType.CONTENT_THANK_YOU,
                    PageClassificationType.MEMBERS_AREA, PageClassificationType.CONTENT_MEMBERS_AREA,
                    PageClassificationType.RECEIPT, # Added Receipt as terminal type
                    PageClassificationType.ORDER_CONFIRMATION
                ])

                # 2. Node has no outgoing links within the graph (dead end)
                has_no_outgoing = not self.graph.get(current_key)

                # Check if path is long enough and meets end conditions
                if len(path) >= min_path_len and (is_terminal_node or has_no_outgoing):
                    path_tuple = tuple(path)
                    path_hash = hash(path_tuple)
                    if path_hash not in visited_paths_hashes:
                        # Convert path keys to (URL, Classifications)
                        flow_details = []
                        valid_path = True
                        for key in path:
                            page = self.page_data.get(key)
                            if page:
                                flow_details.append((page.final_url, page.classifications))
                            else:
                                # Should not happen due to earlier check, but safeguard
                                logger.error(f"Critical: Missing page data for key {key} during final path construction: {path}. Skipping flow.")
                                valid_path = False
                                break
                        if valid_path:
                            potential_flows.append(flow_details)
                            visited_paths_hashes.add(path_hash)
                            logger.debug(f"Found potential flow (len={len(path)}): {' -> '.join(path)}")

                    # Stop exploring further from this node if it's a terminal type
                    if is_terminal_node:
                         continue


                # --- Continue Exploration ---
                # If not at max depth and not a terminal node, explore neighbors
                if len(path) < max_depth:
                    # Get neighbors from graph
                    neighbors = self.graph.get(current_key, set())
                    # Add neighbors to stack if they haven't been visited *in this specific path* to prevent cycles in DFS path list
                    # Process in reverse order to maintain approx left-to-right flow if desired (though graph order isn't guaranteed)
                    for neighbor_key in sorted(list(neighbors), reverse=True):
                        if neighbor_key not in path: # Simple cycle prevention for this path
                            stack.append((neighbor_key, path + [neighbor_key]))
                        # else: logger.debug(f"Cycle detected in path, skipping neighbor {neighbor_key} from {current_key}")


        logger.info(f"Found {len(potential_flows)} potential unique funnel flows.")
        # Sort flows by length (shortest first) then by first URL?
        potential_flows.sort(key=lambda flow: (len(flow), flow[0][0] if flow else ""))
        return potential_flows


    def _identify_entry_points(self) -> List[str]:
        """Identifies potential funnel entry points based on classification and link structure."""
        entry_keys: Set[str] = set()
        if not self.page_data: return []

        # Types commonly initiating a flow
        entry_types = {
            PageClassificationType.LEAD_CAPTURE, PageClassificationType.CONTENT_LEAD_CAPTURE,
            PageClassificationType.CHECKOUT, PageClassificationType.CONTENT_CHECKOUT,
            PageClassificationType.WEBINAR, PageClassificationType.CONTENT_WEBINAR,
            PageClassificationType.ORDER_FORM # Added as potential entry
        }

        # 1. Add the actual starting URL key if it was crawled
        if self.start_url_key in self.page_data:
            entry_keys.add(self.start_url_key)
            logger.debug(f"Added start URL key as entry point: {self.start_url_key}")
        else:
            logger.warning(f"Start URL key {self.start_url_key} (from {self.config.start_url}) not found in crawled page data.")

        # 2. Add pages matching typical entry classifications
        for key, data in self.page_data.items():
            if not entry_types.isdisjoint(data.classifications):
                entry_keys.add(key)

        # 3. Consider pages with low incoming links (orphaned or externally linked)
        #    Build incoming link counts *within the graph*
        incoming_graph_links = defaultdict(int)
        for source_key in self.graph:
             for target_key in self.graph[source_key]:
                  incoming_graph_links[target_key] += 1

        for key, data in self.page_data.items():
            # Add if it has 0 incoming links in the graph (potential orphan/entry)
            # and isn't already added and isn't a common terminal type itself
            is_terminal = any(c in data.classifications for c in [
                PageClassificationType.THANK_YOU, PageClassificationType.CONTENT_THANK_YOU,
                PageClassificationType.MEMBERS_AREA, PageClassificationType.CONTENT_MEMBERS_AREA,
                PageClassificationType.ORDER_CONFIRMATION, PageClassificationType.RECEIPT
            ])

            if key not in entry_keys and not is_terminal and incoming_graph_links.get(key, 0) == 0:
                 # Also check discovery method - maybe prioritize if not found via Guess?
                 discovery_method = self.discovery_log.get(key, "")
                 # Consider pages found via Link/Sitemap/Start/Manual/Redirect more likely entry points than pure Guess/JS finds if they have 0 internal links
                 if discovery_method and not discovery_method.startswith(("Guess", "JavaScript")):
                      logger.debug(f"Adding page with 0 incoming graph links as potential entry point: {key} ({data.final_url}, Discovery: {discovery_method})")
                      entry_keys.add(key)
                 # Optionally add POTENTIAL_HIDDEN pages too? Or pages found via Guess/JS?
                 # elif PageClassificationType.POTENTIAL_HIDDEN in data.classifications:
                 #      entry_keys.add(key)

        # Limit the number of entry points to analyze if too many are found
        limit = 75 # Increased limit slightly
        sorted_entry_keys = sorted(list(entry_keys))

        if len(sorted_entry_keys) > limit:
            logger.warning(f"Found {len(sorted_entry_keys)} potential entry points. Limiting analysis to {limit}.")
            # Prioritize the start URL if present
            prioritized_keys = []
            if self.start_url_key in sorted_entry_keys:
                prioritized_keys.append(self.start_url_key)
            # Add others until limit reached
            for key in sorted_entry_keys:
                if key != self.start_url_key and len(prioritized_keys) < limit:
                    prioritized_keys.append(key)
            final_entry_points = prioritized_keys
        else:
            final_entry_points = sorted_entry_keys

        logger.info(f"Using {len(final_entry_points)} entry points for flow analysis.") #: {final_entry_points}") # Keep log cleaner
        return final_entry_points


# --- Streamlit Specific Functions ---

def prepare_page_details_df(page_data: Dict[str, PageData]) -> pd.DataFrame:
    """Converts page_data dict to a pandas DataFrame for display."""
    if not page_data: return pd.DataFrame()
    rows = []
    for key, data in page_data.items():
        rows.append({
            "Final URL": data.final_url,
            "Status": data.status_code if data.status_code > 0 else data.error_message or "Blocked/Error", # Show error if status 0/-1
            "Title": data.title,
            "Type": data.content_type or "N/A",
            "Classifications": ", ".join(sorted(map(str, data.classifications))),
            "Potential Hidden?": PageClassificationType.POTENTIAL_HIDDEN in data.classifications,
            "Size (Bytes)": data.content_length if data.content_length is not None else "N/A",
            "Forms": data.form_count,
            "Payment Indic?": data.has_payment_indicators,
            "Pricing Indic?": data.has_pricing_indicators,
            "Prices Found": ", ".join(data.prices_found),
            "Discovered By": data.discovery_method,
            "Crawl Key": data.crawl_key, # Added key for reference
            "Error": data.error_message or "",
        })
    # Sort by URL or add option?
    return pd.DataFrame(rows).sort_values(by="Final URL").reset_index(drop=True)

def prepare_page_links_df(page_relationships: Dict[str, Set[Tuple[str, str]]], page_data: Dict[str, PageData]) -> pd.DataFrame:
    """Converts page_relationships to a pandas DataFrame."""
    if not page_relationships: return pd.DataFrame()
    rows = []
    # Pre-build URL -> Key and Key -> Info maps for faster lookups
    url_to_final_data: Dict[str, PageData] = {data.final_url: data for data in page_data.values()}
    key_to_final_data: Dict[str, PageData] = page_data

    for source_key, targets in page_relationships.items():
        source_page_info = key_to_final_data.get(source_key)
        source_url_str = source_page_info.final_url if source_page_info else f"Unknown (Key: {source_key})"

        for target_url_original, link_text in targets:
            # Resolve target URL to find its potential final state
            target_url_resolved = target_url_original
            if source_page_info and not urlparse(target_url_resolved).scheme:
                 try:
                      target_url_resolved = urljoin(source_page_info.final_url, target_url_resolved)
                 except ValueError: pass # Keep original if resolution fails

            if "://" not in target_url_resolved:
                 # Try source scheme first, then default to http
                 scheme = urlparse(source_page_info.final_url).scheme if source_page_info else "http"
                 target_url_resolved = f"{scheme}://{target_url_resolved}"

            target_key = UrlUtils.get_crawl_key(target_url_resolved)
            target_page_info = key_to_final_data.get(target_key)

            target_final_url = target_page_info.final_url if target_page_info else "Not Crawled/Found"
            target_status = target_page_info.status_code if target_page_info else "N/A"
            target_class = ", ".join(sorted(map(str, target_page_info.classifications))) if target_page_info else "N/A"

            rows.append({
                "Source URL": source_url_str,
                "Target Link Found": target_url_original, # Show the href value as found
                "Target Final URL": target_final_url, # Show where it ended up (if crawled)
                "Target Status": target_status,
                "Target Classifications": target_class,
                "Link Text": link_text,
            })
    if not rows: return pd.DataFrame()
    return pd.DataFrame(rows).sort_values(by=["Source URL", "Target Link Found"]).reset_index(drop=True)


def prepare_page_variations_df(page_variations: Dict[str, Set[str]], page_data: Dict[str, PageData], discovery_log: Dict[str, str]) -> pd.DataFrame:
    """Converts page_variations to a pandas DataFrame."""
    if not page_variations: return pd.DataFrame()
    rows = []
    for key, urls in page_variations.items():
        page_info = page_data.get(key)
        final_url_str = page_info.final_url if page_info else "N/A (Key not in final data)"
        title = page_info.title if page_info else "N/A"
        status = page_info.status_code if page_info else "N/A"
        # Use discovery method from page_data if available, else from discovery_log
        discovery = page_info.discovery_method if page_info else discovery_log.get(key, "Unknown")

        # Find which variation was the 'first' discovered for this key (if logged)
        # This logic might be complex if redirects are involved, rely on discovery_log for the key
        # first_discovered_url = next((u for u in urls if UrlUtils.get_crawl_key(u) == key and discovery_log.get(key)), None)


        for url in sorted(list(urls)): # Sort variations for consistent display
             # Check if this specific variant URL matches the final resolved URL for the key
             is_final_url_match = (page_info is not None and url == page_info.final_url)
             rows.append({
                 "Canonical Key": key,
                 "Variant URL Found": url, # URL as found during crawl
                 "Final URL Reached": final_url_str, # Final URL associated with this key
                 "Final Status": status,
                 "Page Title": title,
                 #"Is Final URL?": is_final_url_match,
                 "First Discovered Method (for Key)": discovery,
             })
    if not rows: return pd.DataFrame()
    # Sort by the final URL reached, then by the variant URL
    return pd.DataFrame(rows).sort_values(by=["Final URL Reached", "Variant URL Found"]).reset_index(drop=True)


def format_funnel_flows(potential_flows: List[List[Tuple[str, FrozenSet[PageClassificationType]]]]) -> List[str]:
    """Formats the list of flows into readable strings for Streamlit display."""
    formatted = []
    if not potential_flows: return ["No potential funnel flows identified."]

    for i, flow in enumerate(potential_flows):
        # Create a more compact header
        start_url_short = urlparse(flow[0][0]).path or "/" if flow else "N/A"
        end_url_short = urlparse(flow[-1][0]).path or "/" if flow else "N/A"
        header = f"**Flow {i+1}:** {start_url_short} -> ... -> {end_url_short} ({len(flow)} steps)"
        # Build the detailed flow string for the expander
        flow_str = f"**Full Flow {i+1} (Length: {len(flow)})**\n\n"
        for j, (url, classifications) in enumerate(flow):
             class_str = ", ".join(sorted(map(str, classifications)))
             # Indent steps
             flow_str += f"  {j+1}. `{url}`\n"
             flow_str += f"     *({class_str})*\n"
        # Use markdown container with header and details
        # Use st.expander directly in the main app instead of returning pre-formatted expanders
        formatted.append((header, flow_str))
    return formatted


@st.cache_data # Cache the conversion result
def convert_df_to_csv(df: pd.DataFrame) -> bytes:
   """Converts a Pandas DataFrame to a UTF-8 encoded CSV bytes object."""
   if df.empty:
        return b""
   try:
        buffer = io.StringIO()
        df.to_csv(buffer, index=False, encoding='utf-8', quoting=csv.QUOTE_ALL)
        return buffer.getvalue().encode('utf-8')
   except Exception as e:
        logger.error(f"Error converting DataFrame to CSV: {e}")
        # Fallback to basic CSV conversion
        return df.to_csv(index=False, quoting=csv.QUOTE_ALL).encode('utf-8')


async def run_full_analysis(config: CrawlerConfig, progress_placeholder, status_text_placeholder):
    """Orchestrates the crawling and analysis, returns results."""
    page_data, page_relationships, page_variations, potential_flows = {}, {}, {}, []
    discovery_log = {} # Initialize discovery log
    results = None # Initialize results to None

    try:
        # Define progress callback within the scope
        def update_progress_display(processed, fetched, total, queue_size, status_text="Crawling..."):
            # Update session state (more robust for potential reruns)
            st.session_state.progress_processed = processed
            st.session_state.progress_fetched = fetched
            st.session_state.progress_total = total # This is max_pages
            st.session_state.progress_status = status_text
            st.session_state.queue_size = queue_size # Update queue size in state
            # Update placeholders directly
            # Use processed count for progress bar, as total is max_pages limit
            percentage = min(1.0, (processed / total)) if total > 0 else 0
            progress_placeholder.progress(percentage)
            # Show more detailed status text
            status_text_placeholder.text(f"{status_text} (Processed: {processed}/{total}, Fetched: {fetched}, Queue: {queue_size})")

        classifier = FunnelPageClassifier(config.page_patterns)
        crawler = WebsiteCrawler(config, classifier)
        crawler.set_progress_callback(update_progress_display) # Pass callback

        # Start crawling
        await crawler.crawl()

        # Get results from crawler
        page_data, page_relationships, page_variations = crawler.get_results()
        discovery_log = crawler.discovery_log # Get discovery log

        if not page_data:
            logger.warning("No pages were successfully crawled or data collected.")
            st.warning("Crawling finished, but no page data was collected. Check logs for errors.", icon="⚠️")
            # Update progress to indicate finish state
            update_progress_display(crawler._processed_count, crawler._fetched_count, config.max_pages, 0, "Finished (No data found)")
            return None # Return None if no data

        status_text_placeholder.text("Analyzing funnel flows...")
        progress_placeholder.progress(1.0) # Show 100% during analysis

        # Perform funnel analysis
        analyzer = FunnelAnalyzer(page_data, page_relationships, config, discovery_log) # Pass discovery log
        potential_flows = analyzer.find_potential_funnel_flows(max_depth=8) # Use analyzer's default depth or configure
        logger.info("Funnel analysis complete.")
        update_progress_display(crawler._processed_count, crawler._fetched_count, config.max_pages, 0, "Analysis Complete")

        results = {
            "page_data": page_data,
            "page_relationships": page_relationships,
            "page_variations": page_variations,
            "potential_flows": potential_flows,
            "discovery_log": discovery_log, # Include discovery log in results
            "summary_stats": { # Add summary stats directly
                 "processed": crawler._processed_count,
                 "fetched": crawler._fetched_count,
                 "pages_found": len(page_data),
                 "links_found": sum(len(targets) for targets in page_relationships.values()),
                 "flows_found": len(potential_flows),
                 "errors": sum(1 for d in page_data.values() if d.error_message or d.status_code >= 400),
                 "sitemap_urls": crawler._sitemap_urls_added,
                 "guessed_urls": crawler._guessed_urls_added,
                 "js_urls": crawler._js_urls_added
            }
        }

    except Exception as e:
        logger.exception(f"Critical error during analysis pipeline: {e}")
        st.error(f"Analysis Pipeline Error: {e}", icon="🔥")
        if 'update_progress_display' in locals(): # Check if callback exists
            update_progress_display(st.session_state.get('progress_processed', 0), st.session_state.get('progress_fetched', 0), config.max_pages, st.session_state.get('queue_size', 0), f"Error: {e}")
        else:
             status_text_placeholder.error(f"Analysis failed: {e}")
        return None # Return None on failure

    return results


# --- Streamlit App Layout ---

st.set_page_config(page_title="Elite Funnel Analyzer", layout="wide", initial_sidebar_state="expanded")
st.title("🚀 Elite Sales Funnel Analyzer")
st.markdown("Advanced discovery and analysis of website funnel structures, including subdomains and 'hidden' pages.")

# Initialize Session State more robustly
default_config_values = {
     "start_url": "", "max_pages": 100, "concurrent_requests": 5, "request_delay": 0.8,
     "respect_robots_txt": True, "debug_logging": False, "manual_urls_text": "",
     "find_sitemaps": True, "attempt_url_guessing": True, "analyze_javascript": True, # Enable advanced by default?
     "max_guessed_urls": 15
}

if 'app_initialized' not in st.session_state:
     st.session_state.results = None
     st.session_state.running = False
     st.session_state.progress_processed = 0
     st.session_state.progress_fetched = 0
     st.session_state.progress_total = default_config_values['max_pages']
     st.session_state.progress_status = "Idle"
     st.session_state.queue_size = 0 # For display
     st.session_state.crawl_config_values = default_config_values.copy()
     st.session_state.app_initialized = True
     st.session_state.lxml_warning_shown = False # Reset warning flag

def reset_app_state():
     # Keep config values or reset them too? Resetting seems safer.
     st.session_state.crawl_config_values = default_config_values.copy()
     st.session_state.results = None
     st.session_state.running = False
     st.session_state.progress_processed = 0
     st.session_state.progress_fetched = 0
     st.session_state.progress_total = st.session_state.crawl_config_values['max_pages']
     st.session_state.progress_status = "Idle"
     st.session_state.queue_size = 0
     # Clear placeholders explicitly if they hold state after reset
     # These might need to be defined first in the main layout
     if 'status_placeholder' in globals(): status_placeholder.text("Idle")
     if 'progress_placeholder' in globals(): progress_placeholder.empty()
     logger.info("Streamlit application state reset.")
     st.success("Settings and results reset.")
     time.sleep(1) # Brief pause before rerun
     st.rerun()


# --- Configuration Sidebar ---
with st.sidebar:
    st.header("⚙️ Configuration")
    st.button("Reset All Settings & Results", on_click=reset_app_state, use_container_width=True, key="reset_button", help="Clears results and resets all configuration options to their defaults.")
    st.markdown("---")

    # Use session state for widget values
    st.session_state.crawl_config_values['start_url'] = st.text_input(
        "Starting URL*", value=st.session_state.crawl_config_values['start_url'], placeholder="https://example.com/path")
    st.session_state.crawl_config_values['max_pages'] = st.number_input(
        "Max Pages to Process", min_value=10, max_value=10000, value=st.session_state.crawl_config_values['max_pages'], step=10, help="Maximum number of unique pages to fetch and process. Stops crawl when reached.")
    st.session_state.crawl_config_values['concurrent_requests'] = st.number_input(
        "Concurrency", min_value=1, max_value=50, value=st.session_state.crawl_config_values['concurrent_requests'], step=1, help="Number of simultaneous requests to the server. Higher values crawl faster but increase server load.")
    st.session_state.crawl_config_values['request_delay'] = st.slider(
        "Base Delay Between Requests (s)", min_value=0.0, max_value=10.0, value=st.session_state.crawl_config_values['request_delay'], step=0.1, format="%.1f s", help="Minimum average time to wait between requests (plus random jitter). Helps avoid overloading the server.")

    st.markdown("---")
    st.subheader("Discovery Methods")
    st.session_state.crawl_config_values['respect_robots_txt'] = st.checkbox( "Respect robots.txt", value=st.session_state.crawl_config_values['respect_robots_txt'], help="Follow rules defined in the website's robots.txt file.")
    if not st.session_state.crawl_config_values['respect_robots_txt']:
        st.warning("Ignoring `robots.txt` can overload servers or access restricted areas. Use responsibly.", icon="⚠️")

    st.session_state.crawl_config_values['find_sitemaps'] = st.checkbox("Find & Parse Sitemaps", value=st.session_state.crawl_config_values['find_sitemaps'], help="Look for sitemaps via robots.txt and common locations (/sitemap.xml).")

    st.session_state.crawl_config_values['manual_urls_text'] = st.text_area(
        "Additional Starting URLs", value=st.session_state.crawl_config_values['manual_urls_text'], height=100, placeholder="Enter additional known URLs (e.g., specific landing pages, thank you pages), one per line.", help="Add specific URLs to the crawl queue at the beginning.")

    st.markdown("---")
    st.subheader("Advanced Discovery (Experimental)")
    st.session_state.crawl_config_values['attempt_url_guessing'] = st.checkbox("Attempt URL Guessing", value=st.session_state.crawl_config_values['attempt_url_guessing'], help="Generate and test common funnel page names (e.g., /thank-you, /oto1) relative to found pages.")
    if st.session_state.crawl_config_values['attempt_url_guessing']:
         # st.caption("Tries common paths like /thank-you, /oto1. Can increase crawl time and might find non-existent pages (404s).")
         st.session_state.crawl_config_values['max_guessed_urls'] = st.slider("Max Guesses per Page", 1, 50, st.session_state.crawl_config_values['max_guessed_urls'], help="Maximum number of URLs to guess based on each crawled page.")

    st.session_state.crawl_config_values['analyze_javascript'] = st.checkbox("Analyze JavaScript for Links", value=st.session_state.crawl_config_values['analyze_javascript'], help="Download and scan linked/inline JavaScript files using regular expressions to find potential hidden links or API endpoints.")
    # if st.session_state.crawl_config_values['analyze_javascript']:
    #     st.caption("Downloads linked JS and uses regex to find paths. Increases crawl time and may have false positives.")

    st.markdown("---")
    st.subheader("Debugging")
    st.session_state.crawl_config_values['debug_logging'] = st.checkbox("Enable Debug Logging", value=st.session_state.crawl_config_values['debug_logging'], help="Output detailed logs to the console/log file for troubleshooting.")

    # --- Start Button ---
    start_button = st.button("Start Analysis", type="primary", disabled=st.session_state.running, use_container_width=True, key="start_button")

# --- Main Area ---
# Define placeholders early so reset function can access them if needed
status_placeholder = st.empty()
progress_placeholder = st.empty()

# Persist progress display based on state
status_placeholder.text(
    f"{st.session_state.progress_status} "
    f"(Processed: {st.session_state.progress_processed}/{st.session_state.progress_total}, "
    f"Fetched: {st.session_state.progress_fetched}, Queue: {st.session_state.queue_size})"
)
if st.session_state.running:
    progress_percentage = min(1.0, (st.session_state.progress_processed / st.session_state.progress_total)) if st.session_state.progress_total > 0 else 0
    progress_placeholder.progress(progress_percentage)
# Clear progress bar only if not running AND results exist or final status indicates completion/error
elif not st.session_state.running and (st.session_state.results is not None or any(s in st.session_state.progress_status for s in ["Finished", "Error", "Failed", "Complete"])):
    progress_placeholder.empty()


if start_button:
    # Retrieve values from session state for validation
    cfg_values = st.session_state.crawl_config_values
    url_to_analyze = cfg_values['start_url'].strip()
    manual_urls_raw = cfg_values['manual_urls_text'].splitlines()
    manual_urls_validated = []
    validation_errors = []

    # --- Input Validation ---
    if not url_to_analyze:
        validation_errors.append("Starting URL is required.")
    else:
        try:
            # Call the function to get the URL, ensuring the scheme is present
            temp_url = CrawlerConfig._ensure_scheme(url_to_analyze)

            # -->> Add check here <<--
            if isinstance(temp_url, str):
                # If the returned value is a string, proceed to validate it as a URL
                validated_start_url = temp_url  # Assign it back if needed, or use temp_url directly
                
                # Pydantic validation using appropriate method based on version
                # Use different approach depending on Pydantic version
                if PYDANTIC_V2:
                    # For Pydantic v2
                    from pydantic import TypeAdapter
                    url_validator = TypeAdapter(AnyHttpUrl)
                    url_validator.validate_python(validated_start_url)
                else:
                    # For Pydantic v1 - use constructor to validate
                    AnyHttpUrl(url=validated_start_url)
                # You can add any subsequent code that uses validated_start_url here
            else:
                # If it's not a string (it might be None or another type), raise an error
                # This indicates that _ensure_scheme couldn't produce a valid string URL
                raise ValueError(f"Could not process the input URL: '{url_to_analyze}'. The result after ensuring scheme was not a string (maybe None or invalid input?).")

        except (ValidationError, ValueError) as e:
            # Catch errors from Pydantic validation (ValidationError)
            # or the ValueError raised above if the input wasn't a string
            validation_errors.append(f"Invalid or unprocessable Starting URL: '{url_to_analyze}'. Please enter a valid URL (e.g., https://example.com). Error: {e}")
    # Note: A TypeError should now be less likely to reach here because of the isinstance check,
    # but you could add 'TypeError' to the except clause as an extra safeguard if desired.
    # except TypeError as e:
    #     validation_errors.append(f"A type error occurred unexpectedly while processing URL '{url_to_analyze}'. Error: {e}")

    for i, manual_url in enumerate(manual_urls_raw):
        manual_url = manual_url.strip()
        if manual_url:
            try:
                validated_manual_url = CrawlerConfig._ensure_scheme(manual_url)
                
                # Validate the URL using appropriate Pydantic version method
                if PYDANTIC_V2:
                    # For Pydantic v2
                    from pydantic import TypeAdapter
                    url_validator = TypeAdapter(AnyHttpUrl)
                    validated_url = url_validator.validate_python(validated_manual_url)
                    manual_urls_validated.append(validated_url)
                else:
                    # For Pydantic v1 - use constructor to validate
                    validated_url = AnyHttpUrl(url=validated_manual_url)
                    manual_urls_validated.append(validated_url)
            except (ValidationError, ValueError) as e:
                validation_errors.append(f"Invalid Manual URL (Line {i+1}): {manual_url[:60]}... Error: {e}")

    if validation_errors:
        for error in validation_errors: 
            st.error(error, icon="🚨")
        st.session_state.running = False  # Ensure running is false if validation fails
    else:
        # --- Configuration and Run ---
        st.session_state.running = True
        st.session_state.results = None  # Clear previous results
        st.session_state.progress_processed = 0
        st.session_state.progress_fetched = 0
        st.session_state.progress_total = cfg_values['max_pages']  # Use current config value
        st.session_state.progress_status = "Initializing..."
        st.session_state.queue_size = 0

        # Set Logging Level based on UI checkbox
        log_level = logging.DEBUG if cfg_values['debug_logging'] else logging.INFO
        logging.getLogger("funnel_analyzer_elite").setLevel(log_level)  # Target specific logger
        # Set level for root logger handlers too? Might affect library logs.
        for handler in logging.getLogger("funnel_analyzer_elite").handlers: 
            handler.setLevel(log_level)
        logger.info(f"Log level set to {logging.getLevelName(log_level)}")

        # Prepare Config Object
        try:
            # Pass validated URLs to the config model
            config = CrawlerConfig(
                start_url=url_to_analyze,  # Pass original (validated) string, model re-validates
                manual_urls=[str(url) for url in manual_urls_validated],  # Pass as strings
                max_pages=cfg_values['max_pages'],
                concurrent_requests=cfg_values['concurrent_requests'],
                request_delay=cfg_values['request_delay'],
                respect_robots_txt=cfg_values['respect_robots_txt'],
                find_sitemaps=cfg_values['find_sitemaps'],
                attempt_url_guessing=cfg_values['attempt_url_guessing'],
                analyze_javascript=cfg_values['analyze_javascript'],
                max_guessed_urls_per_page=cfg_values['max_guessed_urls']
                # Add other config params: timeout, retries, jitter, user_agent if needed
            )

            st.info(f"Starting analysis for: {config.start_url} (Max Pages: {config.max_pages})", icon="⏳")
            # Log config using model_dump (Pydantic v2) or dict (Pydantic v1)
            # --- FIX 5: Use Pydantic V2 Flag ---
            config_dict = config.model_dump() if PYDANTIC_V2 else config.dict()
            logger.info(f"Starting analysis run with config: {config_dict}")

            # Use rerun to update UI immediately for progress display before starting async task
            st.rerun()

        except ValidationError as config_err:
            st.error(f"Configuration Error: {config_err}", icon="🔥")
            logger.error(f"Pydantic config validation failed on start: {config_err}")
            st.session_state.running = False
            st.session_state.progress_status = "Config Error"
            st.rerun()  # Rerun to show error and reset button state

# --- Run Analysis if Flagged ---
# This block runs *after* the rerun caused by clicking "Start Analysis" AND validation passing
if st.session_state.running and st.session_state.results is None and st.session_state.progress_status != "Config Error":
    cfg_values = st.session_state.crawl_config_values  # Get config from state
    analysis_results = None  # Initialize
    try:
        # Re-validate and create config object to pass to async function
        # (Ensures consistency if state somehow changed between reruns)
        manual_urls_validated = []
        for url_str in cfg_values['manual_urls_text'].splitlines():
            url_str = url_str.strip()
            if url_str:
                try:
                    validated_manual_url = CrawlerConfig._ensure_scheme(url_str)
                    
                    # Validate the URL using appropriate Pydantic version method
                    if PYDANTIC_V2:
                        # For Pydantic v2
                        from pydantic import TypeAdapter
                        url_validator = TypeAdapter(AnyHttpUrl)
                        validated_url = url_validator.validate_python(validated_manual_url)
                        manual_urls_validated.append(validated_url)
                    else:
                        # For Pydantic v1 - use constructor to validate
                        validated_url = AnyHttpUrl(url=validated_manual_url)
                        manual_urls_validated.append(validated_url)
                except (ValidationError, ValueError): pass  # Ignore invalid ones here, validated before

        config = CrawlerConfig(
            start_url=cfg_values['start_url'],
            manual_urls=[str(url) for url in manual_urls_validated],
            max_pages=cfg_values['max_pages'],
            concurrent_requests=cfg_values['concurrent_requests'],
            request_delay=cfg_values['request_delay'],
            respect_robots_txt=cfg_values['respect_robots_txt'],
            find_sitemaps=cfg_values['find_sitemaps'],
            attempt_url_guessing=cfg_values['attempt_url_guessing'],
            analyze_javascript=cfg_values['analyze_javascript'],
            max_guessed_urls_per_page=cfg_values['max_guessed_urls']
            # Add other params as needed
        )

        # Run the async function within the Streamlit context
        # Streamlit now handles top-level await, but running via asyncio.run is safer for compatibility
        # Need to get or create an event loop for Streamlit context
        try:
            loop = asyncio.get_running_loop()
        except RuntimeError:
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)

        analysis_results = loop.run_until_complete(run_full_analysis(config, progress_placeholder, status_placeholder))

        # Update state after completion/failure
        st.session_state.running = False
        st.session_state.results = analysis_results  # Store results or None if failed

        if analysis_results:
            st.success("Analysis complete!", icon="✅")
        else:
            # Error message handled within run_full_analysis or caught exception below
            if st.session_state.progress_status != "Config Error" and "Error" not in st.session_state.progress_status and "Failed" not in st.session_state.progress_status:
                st.warning("Analysis finished, but no results were generated. Check logs.", icon = "⚠️")


        # Final rerun to display results or final error state
        st.rerun()

    except (ValidationError, Exception) as run_err:
        st.error(f"Failed to start or complete analysis: {run_err}", icon="🔥")
        logger.exception(f"Error recreating config or running analysis task: {run_err}")
        st.session_state.running = False
        st.session_state.results = None  # Ensure no partial results are shown
        st.session_state.progress_status = f"Runtime Error: {run_err}"
        st.rerun()


# --- Display Results ---
if st.session_state.results:
    st.markdown("---")
    st.header("📊 Analysis Results")

    # Extract results for easier access
    results_data = st.session_state.results
    page_data = results_data.get("page_data", {})
    page_relationships = results_data.get("page_relationships", {})
    page_variations = results_data.get("page_variations", {})
    potential_flows = results_data.get("potential_flows", [])
    summary_stats = results_data.get("summary_stats", {})
    discovery_log = results_data.get("discovery_log", {})  # Get discovery log from results

    # Use start URL from config stored in session state for filename consistency
    start_url_for_file = st.session_state.crawl_config_values['start_url']
    try:
        # Generate a clean prefix from the start URL's domain/path
        validated_url_for_file = CrawlerConfig._ensure_scheme(start_url_for_file)
        parsed_start = urlparse(validated_url_for_file)
        file_prefix = f"{parsed_start.netloc.replace(':', '_')}{parsed_start.path.replace('/', '_')}".rstrip('_')
        # Limit length for safety
        file_prefix = re.sub(r'[^\w\-.]', '_', file_prefix)[:50]  # Keep word chars, hyphen, dot
    except Exception as file_parse_err:
        logger.warning(f"Could not parse start URL for file prefix: {file_parse_err}")
        file_prefix = "funnel_analysis"  # Fallback

    st.subheader("Crawl Summary")
    col1, col2, col3, col4 = st.columns(4)
    col1.metric("Pages Found", summary_stats.get('pages_found', 0))
    col2.metric("Links Found", summary_stats.get('links_found', 0))
    col3.metric("Potential Flows", summary_stats.get('flows_found', 0))
    col4.metric("Pages with Errors", summary_stats.get('errors', 0))

    # Optional: Display discovery stats
    with st.expander("Discovery Statistics"):
        st.metric("Sitemap URLs Added", summary_stats.get('sitemap_urls', 0))
        st.metric("Guessed URLs Added", summary_stats.get('guessed_urls', 0))
        st.metric("JavaScript URLs Added", summary_stats.get('js_urls', 0))
        st.metric("Total URLs Processed", summary_stats.get('processed', 0))


    tab_pages, tab_links, tab_flows, tab_variations = st.tabs([
        f"📄 Pages ({summary_stats.get('pages_found', 0)})",
        f"🔗 Links ({summary_stats.get('links_found', 0)})",
        f"🌊 Flows ({summary_stats.get('flows_found', 0)})",
        f"🎭 Variations ({sum(len(v) for v in page_variations.values())})"
    ])

    with tab_pages:
        st.subheader("Crawled Page Details")
        if page_data:
            df_pages = prepare_page_details_df(page_data)
            st.dataframe(df_pages, use_container_width=True, height=400)
            csv_pages = convert_df_to_csv(df_pages)
            if csv_pages:
                st.download_button(label="Download Page Details (CSV)", data=csv_pages,
                                  file_name=f"page_details_{file_prefix}.csv", mime="text/csv")
            else: st.warning("Could not generate CSV for Page Details.")
        else: st.info("No page data available.")

    with tab_links:
        st.subheader("Page Links (Internal)")
        if page_relationships:
            df_links = prepare_page_links_df(page_relationships, page_data)
            st.dataframe(df_links, use_container_width=True, height=400)
            csv_links = convert_df_to_csv(df_links)
            if csv_links:
                st.download_button(label="Download Page Links (CSV)", data=csv_links,
                                  file_name=f"page_links_{file_prefix}.csv", mime="text/csv")
            else: st.warning("Could not generate CSV for Page Links.")
        else: st.info("No internal link data available (or no links found between crawled pages).")

    with tab_flows:
        st.subheader("Potential Funnel Flows")
        if potential_flows:
            formatted_flows = format_funnel_flows(potential_flows)
            if formatted_flows and isinstance(formatted_flows[0], tuple):
                # Display flows in expanders
                for header, details in formatted_flows:
                    with st.expander(header):
                        st.markdown(details, unsafe_allow_html=False)  # Keep unsafe_allow_html=False

                # Prepare DataFrame for download
                flow_rows = []
                for i, flow in enumerate(potential_flows):
                    for j, (url, classifications) in enumerate(flow):
                        class_str = ", ".join(sorted(map(str, classifications)))
                        flow_rows.append({"Flow Number": i+1, "Step": j+1, "URL": url, "Classifications": class_str})
                if flow_rows:
                    df_flows = pd.DataFrame(flow_rows)
                    csv_flows = convert_df_to_csv(df_flows)
                    if csv_flows:
                        st.download_button(label="Download Funnel Flows (CSV)", data=csv_flows,
                                          file_name=f"funnel_flows_{file_prefix}.csv", mime="text/csv")
                    else: st.warning("Could not generate CSV for Funnel Flows.")
                else: st.info("Flow data found but could not be formatted for download.")
            else:
                st.info(formatted_flows[0])  # Display "No flows identified" message
        else: st.info("No potential funnel flows identified.")

    with tab_variations:
        st.subheader("Page URL Variations")
        st.markdown("Shows different URLs found during the crawl that ultimately led to the same canonical page content (after removing tracking parameters, normalizing paths, etc.). Useful for identifying duplicate content sources.")
        if page_variations:
            df_variations = prepare_page_variations_df(page_variations, page_data, discovery_log)  # Pass discovery_log
            st.dataframe(df_variations, use_container_width=True, height=400)
            csv_variations = convert_df_to_csv(df_variations)
            if csv_variations:
                st.download_button(label="Download Page Variations (CSV)", data=csv_variations,
                                  file_name=f"page_variations_{file_prefix}.csv", mime="text/csv")
            else: st.warning("Could not generate CSV for Page Variations.")
        else: st.info("No page variations recorded (or only canonical URLs were found).")

# Add a footer or info section
st.markdown("---")
st.caption("Elite Funnel Analyzer v3.0 - Use responsibly and respect website terms of service.")
